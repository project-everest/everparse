#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub type cbordet <'a> = crate::cbordetveraux::cbor_raw <'a>;

pub fn cbor_det_reset_perm <'a>(x: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{
    let x·: crate::cbordetveraux::cbor_raw = crate::cbordetveraux::cbor_raw_reset_perm(x);
    x·
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·CBOR_Pulse_Raw_EverParse_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (crate::cbordetveraux::cbor_raw <'a>, &'a [u8]) }
}

pub fn cbor_det_parse <'a>(input: &'a [u8]) ->
    option__·CBOR_Pulse_Raw_EverParse_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let len: usize = crate::cbordetveraux::cbor_validate_det(input);
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
        let input2: &[u8] = _letpattern.0;
        let rem: &[u8] = _letpattern.1;
        let len1: usize = input2.len();
        crate::lowstar::ignore::ignore::<usize>(len1);
        let res: crate::cbordetveraux::cbor_raw = crate::cbordetveraux::cbor_parse_valid(input2);
        option__·CBOR_Pulse_Raw_EverParse_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: (res,rem) }
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__size_t
{
    None,
    Some { v: usize }
}

pub fn cbor_det_size(x: crate::cbordetveraux::cbor_raw, bound: usize) -> option__size_t
{
    let size: usize = crate::cbordetveraux::cbor_size(x, bound);
    if size == 0usize { option__size_t::None } else { option__size_t::Some { v: size } }
}

pub fn cbor_det_serialize(x: crate::cbordetveraux::cbor_raw, output: &mut [u8]) ->
    option__size_t
{
    let size: usize = crate::cbordetveraux::cbor_size(x, output.len());
    if size > 0usize
    {
        let _letpattern: (&mut [u8], &mut [u8]) = output.split_at_mut(size);
        let out: &mut [u8] = _letpattern.0;
        let _rem: &[u8] = _letpattern.1;
        crate::lowstar::ignore::ignore::<usize>(
            crate::cbordetveraux::cbor_det_serialize_slice(x, out)
        );
        option__size_t::Some { v: size }
    }
    else
    { option__size_t::None }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>
{
    None,
    Some { v: crate::cbordetveraux::cbor_raw <'a> }
}

pub fn cbor_det_mk_simple_value <'a>(v: u8) ->
    option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    if
    v <= crate::cbordetveraux::max_simple_value_additional_info
    ||
    crate::cbordetveraux::min_simple_value_long_argument <= v
    {
        let res: crate::cbordetveraux::cbor_raw = crate::cbordetveraux::cbor_mk_simple_value(v);
        option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Some { v: res }
    }
    else
    { option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::None }
}

#[derive(PartialEq, Clone, Copy)]
pub enum cbor_det_int_kind
{
    UInt64,
    NegInt64
}

pub fn cbor_det_mk_int64 <'a>(ty: cbor_det_int_kind, v: u64) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{
    let ite: u8 =
        if ty == cbor_det_int_kind::UInt64
        { crate::cbordetveraux::cbor_major_type_uint64 }
        else
        { crate::cbordetveraux::cbor_major_type_neg_int64 };
    crate::cbordetveraux::cbor_mk_int64(ite, v)
}

#[derive(PartialEq, Clone, Copy)]
pub enum cbor_det_string_kind
{
    ByteString,
    TextString
}

pub fn cbor_impl_utf8_correct(s: &[u8]) -> bool { crate::cbordetveraux::impl_correct(s) }

pub fn cbor_det_mk_string <'a>(ty: cbor_det_string_kind, s: &'a [u8]) ->
    option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    if s.len() > 18446744073709551615u64 as usize
    { option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::None }
    else
    {
        let correct: bool =
            if ty == cbor_det_string_kind::TextString { cbor_impl_utf8_correct(s) } else { true };
        if correct
        {
            let len64: crate::cbordetveraux::raw_uint64 =
                crate::cbordetveraux::mk_raw_uint64(s.len() as u64);
            crate::lowstar::ignore::ignore::<crate::cbordetveraux::raw_uint64>(len64);
            let ite: u8 =
                if ty == cbor_det_string_kind::ByteString
                { crate::cbordetveraux::cbor_major_type_byte_string }
                else
                { crate::cbordetveraux::cbor_major_type_text_string };
            let res: crate::cbordetveraux::cbor_raw = crate::cbordetveraux::cbor_mk_string(ite, s);
            let res0: crate::cbordetveraux::cbor_raw = res;
            option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Some { v: res0 }
        }
        else
        { option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::None }
    }
}

pub fn cbor_det_mk_tagged <'a>(tag: u64, r: &'a [crate::cbordetveraux::cbor_raw <'a>]) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{
    let tag64: crate::cbordetveraux::raw_uint64 = crate::cbordetveraux::mk_raw_uint64(tag);
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::raw_uint64>(tag64);
    let res: crate::cbordetveraux::cbor_raw = crate::cbordetveraux::cbor_mk_tagged(tag, r);
    res
}

pub type cbor_det_map_entry <'a> =
crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>;

pub fn cbor_det_mk_map_entry <'a>(
    xk: crate::cbordetveraux::cbor_raw <'a>,
    xv: crate::cbordetveraux::cbor_raw <'a>
) ->
    crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    let xk·: crate::cbordetveraux::cbor_raw = crate::cbordetveraux::cbor_raw_reset_perm(xk);
    let xv·: crate::cbordetveraux::cbor_raw = crate::cbordetveraux::cbor_raw_reset_perm(xv);
    let res: crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
        crate::cbordetveraux::cbor_mk_map_entry(xk·, xv·);
    res
}

pub fn cbor_det_mk_array <'a>(a: &'a [crate::cbordetveraux::cbor_raw <'a>]) ->
    option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    if a.len() > 18446744073709551615u64 as usize
    { option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::None }
    else
    {
        let bml: crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
            { ss: a };
        let ml: crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
            crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
            { _0: bml };
        let len_sz: usize = a.len();
        let len64: u64 = len_sz as u64;
        let ru: crate::cbordetveraux::raw_uint64 = crate::cbordetveraux::mk_raw_uint64(len64);
        let res: crate::cbordetveraux::cbor_raw = crate::cbordetveraux::cbor_mk_array(ru.size, ml);
        let res0: crate::cbordetveraux::cbor_raw = res;
        option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Some { v: res0 }
    }
}

pub fn cbor_det_mk_map <'a>(
    a: &'a mut [crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>]
) ->
    option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    let mut dest: [crate::cbordetveraux::cbor_raw; 1] =
        [crate::cbordetveraux::cbor_raw::CBOR_Case_Simple { v: 0u8 }; 1usize];
    let bres: bool =
        if a.len() > 18446744073709551615u64 as usize
        { false }
        else
        {
            let correct: bool = crate::cbordetveraux::cbor_raw_sort(a);
            if correct
            {
                let
                bml:
                crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                =
                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                    { ss: a };
                let
                ml:
                crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                =
                    crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                    { _0: bml };
                let len_sz: usize = a.len();
                let len64: u64 = len_sz as u64;
                let raw_len: crate::cbordetveraux::raw_uint64 =
                    crate::cbordetveraux::mk_raw_uint64(len64);
                let res: crate::cbordetveraux::cbor_raw =
                    crate::cbordetveraux::cbor_mk_map(raw_len.size, ml);
                (&mut dest)[0] = res;
                true
            }
            else
            { false }
        };
    if bres
    {
        let res: crate::cbordetveraux::cbor_raw = (&dest)[0];
        option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Some { v: res }
    }
    else
    { option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::None }
}

pub fn cbor_det_equal(x1: crate::cbordetveraux::cbor_raw, x2: crate::cbordetveraux::cbor_raw) ->
    bool
{
    let comp: i16 = crate::cbordetveraux::impl_cbor_compare(x1, x2);
    comp == 0i16
}

pub fn cbor_det_major_type(x: crate::cbordetveraux::cbor_raw) -> u8
{ crate::cbordetveraux::cbor_raw_get_major_type(x) }

pub type cbor_det_array <'a> = crate::cbordetveraux::cbor_raw <'a>;

pub type cbor_det_map <'a> = crate::cbordetveraux::cbor_raw <'a>;

#[derive(PartialEq, Clone, Copy)]
enum cbor_det_view_tags
{
    Int64,
    String,
    Array,
    Map,
    Tagged,
    SimpleValue
}

#[derive(PartialEq, Clone, Copy)]
pub enum cbor_det_view <'a>
{
    Int64 { kind: cbor_det_int_kind, value: u64 },
    String { kind: cbor_det_string_kind, payload: &'a [u8] },
    Array { _0: crate::cbordetveraux::cbor_raw <'a> },
    Map { _0: crate::cbordetveraux::cbor_raw <'a> },
    Tagged { tag: u64, payload: crate::cbordetveraux::cbor_raw <'a> },
    SimpleValue { _0: u8 }
}

pub fn cbor_det_destruct <'a>(c: crate::cbordetveraux::cbor_raw <'a>) -> cbor_det_view <'a>
{
    let ty: u8 = crate::cbordetveraux::cbor_raw_get_major_type(c);
    if
    ty == crate::cbordetveraux::cbor_major_type_uint64
    ||
    ty == crate::cbordetveraux::cbor_major_type_neg_int64
    {
        let k: cbor_det_int_kind =
            if ty == crate::cbordetveraux::cbor_major_type_uint64
            { cbor_det_int_kind::UInt64 }
            else
            { cbor_det_int_kind::NegInt64 };
        let i: u64 = crate::cbordetveraux::cbor_raw_read_int64_value(c);
        cbor_det_view::Int64 { kind: k, value: i }
    }
    else if
    ty == crate::cbordetveraux::cbor_major_type_byte_string
    ||
    ty == crate::cbordetveraux::cbor_major_type_text_string
    {
        let k: cbor_det_string_kind =
            if ty == crate::cbordetveraux::cbor_major_type_byte_string
            { cbor_det_string_kind::ByteString }
            else
            { cbor_det_string_kind::TextString };
        let sl: &[u8] = crate::cbordetveraux::cbor_raw_get_string(c);
        cbor_det_view::String { kind: k, payload: sl }
    }
    else if ty == crate::cbordetveraux::cbor_major_type_array
    {
        let res: crate::cbordetveraux::cbor_raw = c;
        cbor_det_view::Array { _0: res }
    }
    else if ty == crate::cbordetveraux::cbor_major_type_map
    {
        let res: crate::cbordetveraux::cbor_raw = c;
        cbor_det_view::Map { _0: res }
    }
    else if ty == crate::cbordetveraux::cbor_major_type_tagged
    {
        let tag: u64 = crate::cbordetveraux::cbor_raw_read_tagged_tag(c);
        let payload: crate::cbordetveraux::cbor_raw =
            crate::cbordetveraux::cbor_raw_get_tagged_payload(c);
        cbor_det_view::Tagged { tag, payload }
    }
    else
    {
        let i: u8 = crate::cbordetveraux::cbor_raw_read_simple_value(c);
        cbor_det_view::SimpleValue { _0: i }
    }
}

pub fn cbor_det_get_array_length(x: crate::cbordetveraux::cbor_raw) -> u64
{ crate::cbordetveraux::cbor_raw_read_array_length(x) }

pub type cbor_det_array_iterator_t <'a> =
crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>;

pub fn cbor_det_array_iterator_start <'a>(x: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    let ml: crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
        crate::cbordetveraux::cbor_raw_get_array(x);
    let total_sz: usize =
        crate::cbordetveraux::mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
    if total_sz == 0usize
    {
        crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IBase
        {
            before:
            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
        }
    }
    else
    {
        let
        mut r_node: [crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw; 1]
        =
            [ml; 1usize];
        let mut r_off: [usize; 1] = [0usize; 1usize];
        let mut r_n: [usize; 1] = [total_sz; 1usize];
        let mut pcontinue: [bool; 1] =
            [! crate::cbordetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
                1usize];
        while
        (&pcontinue)[0]
        {
            let node: crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                (&r_node)[0];
            let cur_off_v: usize = (&r_off)[0];
            let cur_n_v: usize = (&r_n)[0];
            match node
            {
                crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                { cb, ca, ob, before, oa, after }
                =>
                  {
                      let child_n_before: usize =
                          crate::cbordetveraux::append_n_before_sz(cur_off_v, cur_n_v, cb);
                      if child_n_before > 0usize
                      {
                          let child_off_sz: usize =
                              crate::cbordetveraux::append_off_before_sz(cur_off_v, ob, cb);
                          let
                          ib:
                          crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                          =
                              before[0];
                          (&mut r_node)[0] = ib;
                          (&mut r_off)[0] = child_off_sz;
                          (&mut r_n)[0] = child_n_before;
                          (&mut pcontinue)[0] =
                              !
                              crate::cbordetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                  ib
                              )
                      }
                      else
                      {
                          let child_off_sz: usize =
                              crate::cbordetveraux::append_off_after_sz(cur_off_v, oa, ca, cb);
                          let child_n_sz: usize =
                              crate::cbordetveraux::append_n_after_sz(cur_off_v, cur_n_v, cb);
                          let
                          ia:
                          crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                          =
                              after[0];
                          (&mut r_node)[0] = ia;
                          (&mut r_off)[0] = child_off_sz;
                          (&mut r_n)[0] = child_n_sz;
                          (&mut pcontinue)[0] =
                              !
                              crate::cbordetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                  ia
                              )
                      }
                  },
                crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                { .. }
                => (),
                _ => panic!("Incomplete pattern matching")
            }
        };
        let node: crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
            (&r_node)[0];
        let cur_off_v: usize = (&r_off)[0];
        let cur_n_v: usize = (&r_n)[0];
        let
        res: (crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw, usize)
        =
            match node
            {
                crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                { _0: bi }
                =>
                  {
                      let
                      bi·:
                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                      =
                          match bi
                          {
                              crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                              =>
                                crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                              crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                              { sr: s }
                              =>
                                if cur_n_v == 0usize
                                {
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                }
                                else
                                {
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                    { sr: s }
                                },
                              crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                              { ss: s }
                              =>
                                {
                                    let
                                    s_pr:
                                    (&[crate::cbordetveraux::cbor_raw],
                                    &[crate::cbordetveraux::cbor_raw])
                                    =
                                        s.split_at(cur_off_v);
                                    let _s_prefix: &[crate::cbordetveraux::cbor_raw] = s_pr.0;
                                    let s_rest: &[crate::cbordetveraux::cbor_raw] = s_pr.1;
                                    let
                                    s_ms:
                                    (&[crate::cbordetveraux::cbor_raw],
                                    &[crate::cbordetveraux::cbor_raw])
                                    =
                                        s_rest.split_at(cur_n_v);
                                    let s_middle: &[crate::cbordetveraux::cbor_raw] = s_ms.0;
                                    let _s_suffix: &[crate::cbordetveraux::cbor_raw] = s_ms.1;
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                    { ss: s_middle }
                                },
                              crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
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
                                            crate::cbordetveraux::jump_raw_data_item_eta(pl, offset);
                                        (&mut pn)[0] = n0.wrapping_sub(1usize);
                                        (&mut poffset)[0] = offset·;
                                        let n1: usize = (&pn)[0];
                                        cond = n1 > 0usize
                                    };
                                    let pos: usize = (&poffset)[0];
                                    let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                    let _pl_prefix: &[u8] = pl_p.0;
                                    let pl_suffix: &[u8] = pl_p.1;
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                    { count: cur_n_v, payload: pl_suffix }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      let len: usize =
                          crate::cbordetveraux::base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                              bi·
                          );
                      (bi·,len)
                  },
                crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                { .. }
                => panic!("Pulse.Lib.Dv.unreachable"),
                _ => panic!("Incomplete pattern matching")
            };
        let bi·: crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
            crate::cbordetveraux::fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                res
            );
        let len_sz: usize =
            crate::cbordetveraux::snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                res
            );
        let rest_sz: usize = total_sz.wrapping_sub(len_sz);
        let rest: crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
            match ml
            {
                crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                { _0: bi }
                =>
                  {
                      let
                      bi·1:
                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                      =
                          match bi
                          {
                              crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                              =>
                                crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                              crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                              { sr: s }
                              =>
                                if rest_sz == 0usize
                                {
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                }
                                else
                                {
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                    { sr: s }
                                },
                              crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                              { ss: s }
                              =>
                                {
                                    let
                                    s_pr:
                                    (&[crate::cbordetveraux::cbor_raw],
                                    &[crate::cbordetveraux::cbor_raw])
                                    =
                                        s.split_at(len_sz);
                                    let _s_prefix: &[crate::cbordetveraux::cbor_raw] = s_pr.0;
                                    let s_rest: &[crate::cbordetveraux::cbor_raw] = s_pr.1;
                                    let
                                    s_ms:
                                    (&[crate::cbordetveraux::cbor_raw],
                                    &[crate::cbordetveraux::cbor_raw])
                                    =
                                        s_rest.split_at(rest_sz);
                                    let s_middle: &[crate::cbordetveraux::cbor_raw] = s_ms.0;
                                    let _s_suffix: &[crate::cbordetveraux::cbor_raw] = s_ms.1;
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                    { ss: s_middle }
                                },
                              crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
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
                                            crate::cbordetveraux::jump_raw_data_item_eta(pl, offset);
                                        (&mut pn)[0] = n0.wrapping_sub(1usize);
                                        (&mut poffset)[0] = offset·;
                                        let n1: usize = (&pn)[0];
                                        cond = n1 > 0usize
                                    };
                                    let pos: usize = (&poffset)[0];
                                    let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                    let _pl_prefix: &[u8] = pl_p.0;
                                    let pl_suffix: &[u8] = pl_p.1;
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                    { count: rest_sz, payload: pl_suffix }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                      { _0: bi·1 }
                  },
                crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                { cb, ca, ob, before, oa, after }
                =>
                  {
                      let cb·_sz: usize =
                          crate::cbordetveraux::append_n_before_sz(len_sz, rest_sz, cb);
                      let ca·_sz: usize =
                          crate::cbordetveraux::append_n_after_sz(len_sz, rest_sz, cb);
                      let ob·_sz: usize =
                          crate::cbordetveraux::append_off_before_sz(len_sz, ob, cb);
                      let oa·_sz: usize =
                          crate::cbordetveraux::append_off_after_sz(len_sz, oa, ca, cb);
                      crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                      { cb: cb·_sz, ca: ca·_sz, ob: ob·_sz, before, oa: oa·_sz, after }
                  },
                _ => panic!("Incomplete pattern matching")
            };
        crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IPair
        { before: bi·, after: rest }
    }
}

pub fn cbor_det_array_iterator_is_empty(
    x: crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
) ->
    bool
{
    match x
    {
        crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IBase
        { before: bi }
        =>
          {
              let len_before: usize =
                  crate::cbordetveraux::base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                      bi
                  );
              len_before == 0usize
          },
        crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IPair
        { before: bi, .. }
        =>
          {
              let len_before: usize =
                  crate::cbordetveraux::base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                      bi
                  );
              len_before == 0usize
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn cbor_det_array_iterator_next <'a>(
    x: crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>
) ->
    (crate::cbordetveraux::cbor_raw
    <'a>,
    crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>)
{
    let mut r: [crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw; 1] =
        [x; 1usize];
    let i_cur: crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw = (&r)[0];
    let
    _letpattern:
    (crate::cbordetveraux::cbor_raw,
    crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw)
    =
        crate::cbordetveraux::iterator_next_raw_data_item(i_cur);
    let elt: crate::cbordetveraux::cbor_raw =
        {
            let res: crate::cbordetveraux::cbor_raw = _letpattern.0;
            let it·: crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                _letpattern.1;
            (&mut r)[0] = it·;
            res
        };
    let x·: crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw = (&r)[0];
    (elt,x·)
}

pub fn cbor_det_array_iterator_length(
    x: crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
) ->
    u64
{
    match x
    {
        crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IBase
        { before: bi }
        =>
          {
              let len_before: usize =
                  crate::cbordetveraux::base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                      bi
                  );
              len_before as u64
          },
        crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IPair
        { before: bi, after: ml }
        =>
          {
              let len_before: usize =
                  crate::cbordetveraux::base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                      bi
                  );
              let len_after: usize =
                  crate::cbordetveraux::mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                      ml
                  );
              let len_total: usize = len_before.wrapping_add(len_after);
              len_total as u64
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn cbor_det_array_iterator_truncate <'a>(
    x: crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>,
    len: u64
) ->
    crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    let len_sz: usize = len as usize;
    match x
    {
        crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IBase
        { before: bi }
        =>
          {
              let cb_sz: usize =
                  crate::cbordetveraux::base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                      bi
                  );
              crate::lowstar::ignore::ignore::<usize>(cb_sz);
              let
              bi·: crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              =
                  match bi
                  {
                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                      =>
                        crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                      { sr: s }
                      =>
                        if len_sz == 0usize
                        {
                            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                        }
                        else
                        {
                            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                            { sr: s }
                        },
                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                      { ss: s }
                      =>
                        {
                            let
                            s_pr:
                            (&[crate::cbordetveraux::cbor_raw], &[crate::cbordetveraux::cbor_raw])
                            =
                                s.split_at(0usize);
                            let _s_prefix: &[crate::cbordetveraux::cbor_raw] = s_pr.0;
                            let s_rest: &[crate::cbordetveraux::cbor_raw] = s_pr.1;
                            let
                            s_ms:
                            (&[crate::cbordetveraux::cbor_raw], &[crate::cbordetveraux::cbor_raw])
                            =
                                s_rest.split_at(len_sz);
                            let s_middle: &[crate::cbordetveraux::cbor_raw] = s_ms.0;
                            let _s_suffix: &[crate::cbordetveraux::cbor_raw] = s_ms.1;
                            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                            { ss: s_middle }
                        },
                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                      { payload: pl, .. }
                      =>
                        {
                            let mut pn: [usize; 1] = [0usize; 1usize];
                            let mut poffset: [usize; 1] = [0usize; 1usize];
                            let n1: usize = (&pn)[0];
                            let mut cond: bool = n1 > 0usize;
                            while
                            cond
                            {
                                let n10: usize = (&pn)[0];
                                let offset: usize = (&poffset)[0];
                                let offset·: usize =
                                    crate::cbordetveraux::jump_raw_data_item_eta(pl, offset);
                                (&mut pn)[0] = n10.wrapping_sub(1usize);
                                (&mut poffset)[0] = offset·;
                                let n11: usize = (&pn)[0];
                                cond = n11 > 0usize
                            };
                            let pos: usize = (&poffset)[0];
                            let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                            let _pl_prefix: &[u8] = pl_p.0;
                            let pl_suffix: &[u8] = pl_p.1;
                            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                            { count: len_sz, payload: pl_suffix }
                        },
                      _ => panic!("Incomplete pattern matching")
                  };
              crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IBase
              { before: bi· }
          },
        crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IPair
        { before: bi, after: ml }
        =>
          {
              let cb_sz: usize =
                  crate::cbordetveraux::base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                      bi
                  );
              let len_before_sz: usize = if len_sz <= cb_sz { len_sz } else { cb_sz };
              let len_after_sz: usize =
                  if len_sz <= cb_sz { 0usize } else { len_sz.wrapping_sub(cb_sz) };
              let
              bi·: crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              =
                  match bi
                  {
                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                      =>
                        crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                      { sr: s }
                      =>
                        if len_before_sz == 0usize
                        {
                            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                        }
                        else
                        {
                            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                            { sr: s }
                        },
                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                      { ss: s }
                      =>
                        {
                            let
                            s_pr:
                            (&[crate::cbordetveraux::cbor_raw], &[crate::cbordetveraux::cbor_raw])
                            =
                                s.split_at(0usize);
                            let _s_prefix: &[crate::cbordetveraux::cbor_raw] = s_pr.0;
                            let s_rest: &[crate::cbordetveraux::cbor_raw] = s_pr.1;
                            let
                            s_ms:
                            (&[crate::cbordetveraux::cbor_raw], &[crate::cbordetveraux::cbor_raw])
                            =
                                s_rest.split_at(len_before_sz);
                            let s_middle: &[crate::cbordetveraux::cbor_raw] = s_ms.0;
                            let _s_suffix: &[crate::cbordetveraux::cbor_raw] = s_ms.1;
                            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                            { ss: s_middle }
                        },
                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                      { payload: pl, .. }
                      =>
                        {
                            let mut pn: [usize; 1] = [0usize; 1usize];
                            let mut poffset: [usize; 1] = [0usize; 1usize];
                            let n1: usize = (&pn)[0];
                            let mut cond: bool = n1 > 0usize;
                            while
                            cond
                            {
                                let n10: usize = (&pn)[0];
                                let offset: usize = (&poffset)[0];
                                let offset·: usize =
                                    crate::cbordetveraux::jump_raw_data_item_eta(pl, offset);
                                (&mut pn)[0] = n10.wrapping_sub(1usize);
                                (&mut poffset)[0] = offset·;
                                let n11: usize = (&pn)[0];
                                cond = n11 > 0usize
                            };
                            let pos: usize = (&poffset)[0];
                            let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                            let _pl_prefix: &[u8] = pl_p.0;
                            let pl_suffix: &[u8] = pl_p.1;
                            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                            { count: len_before_sz, payload: pl_suffix }
                        },
                      _ => panic!("Incomplete pattern matching")
                  };
              let ca_sz: usize =
                  crate::cbordetveraux::mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                      ml
                  );
              crate::lowstar::ignore::ignore::<usize>(ca_sz);
              let
              after·: crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              =
                  match ml
                  {
                      crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                      { _0: bi1 }
                      =>
                        {
                            let
                            bi·1:
                            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                            =
                                match bi1
                                {
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                    =>
                                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                    { sr: s }
                                    =>
                                      if len_after_sz == 0usize
                                      {
                                          crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                      }
                                      else
                                      {
                                          crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                          { sr: s }
                                      },
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                    { ss: s }
                                    =>
                                      {
                                          let
                                          s_pr:
                                          (&[crate::cbordetveraux::cbor_raw],
                                          &[crate::cbordetveraux::cbor_raw])
                                          =
                                              s.split_at(0usize);
                                          let _s_prefix: &[crate::cbordetveraux::cbor_raw] = s_pr.0;
                                          let s_rest: &[crate::cbordetveraux::cbor_raw] = s_pr.1;
                                          let
                                          s_ms:
                                          (&[crate::cbordetveraux::cbor_raw],
                                          &[crate::cbordetveraux::cbor_raw])
                                          =
                                              s_rest.split_at(len_after_sz);
                                          let s_middle: &[crate::cbordetveraux::cbor_raw] = s_ms.0;
                                          let _s_suffix: &[crate::cbordetveraux::cbor_raw] = s_ms.1;
                                          crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                          { ss: s_middle }
                                      },
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                    { payload: pl, .. }
                                    =>
                                      {
                                          let mut pn: [usize; 1] = [0usize; 1usize];
                                          let mut poffset: [usize; 1] = [0usize; 1usize];
                                          let n1: usize = (&pn)[0];
                                          let mut cond: bool = n1 > 0usize;
                                          while
                                          cond
                                          {
                                              let n10: usize = (&pn)[0];
                                              let offset: usize = (&poffset)[0];
                                              let offset·: usize =
                                                  crate::cbordetveraux::jump_raw_data_item_eta(
                                                      pl,
                                                      offset
                                                  );
                                              (&mut pn)[0] = n10.wrapping_sub(1usize);
                                              (&mut poffset)[0] = offset·;
                                              let n11: usize = (&pn)[0];
                                              cond = n11 > 0usize
                                          };
                                          let pos: usize = (&poffset)[0];
                                          let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                          let _pl_prefix: &[u8] = pl_p.0;
                                          let pl_suffix: &[u8] = pl_p.1;
                                          crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                          { count: len_after_sz, payload: pl_suffix }
                                      },
                                    _ => panic!("Incomplete pattern matching")
                                };
                            crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                            { _0: bi·1 }
                        },
                      crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                      { cb, ca, ob, before, oa, after }
                      =>
                        {
                            let cb·_sz: usize =
                                crate::cbordetveraux::append_n_before_sz(0usize, len_after_sz, cb);
                            let ca·_sz: usize =
                                crate::cbordetveraux::append_n_after_sz(0usize, len_after_sz, cb);
                            let ob·_sz: usize =
                                crate::cbordetveraux::append_off_before_sz(0usize, ob, cb);
                            let oa·_sz: usize =
                                crate::cbordetveraux::append_off_after_sz(0usize, oa, ca, cb);
                            crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                            { cb: cb·_sz, ca: ca·_sz, ob: ob·_sz, before, oa: oa·_sz, after }
                        },
                      _ => panic!("Incomplete pattern matching")
                  };
              crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IPair
              { before: bi·, after: after· }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn cbor_det_get_array_item <'a>(x: crate::cbordetveraux::cbor_raw <'a>, i: u64) ->
    option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    let len: u64 = cbor_det_get_array_length(x);
    if i >= len
    { option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::None }
    else
    {
        let ml: crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
            crate::cbordetveraux::cbor_raw_get_array(x);
        let total_sz: usize =
            crate::cbordetveraux::mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
        let it: crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
            if total_sz == 0usize
            {
                crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IBase
                {
                    before:
                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                }
            }
            else
            {
                let
                mut
                r_node:
                [crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw; 1]
                =
                    [ml; 1usize];
                let mut r_off: [usize; 1] = [0usize; 1usize];
                let mut r_n: [usize; 1] = [total_sz; 1usize];
                let mut pcontinue: [bool; 1] =
                    [!
                        crate::cbordetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                            ml
                        );
                        1usize];
                while
                (&pcontinue)[0]
                {
                    let
                    node: crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                    =
                        (&r_node)[0];
                    let cur_off_v: usize = (&r_off)[0];
                    let cur_n_v: usize = (&r_n)[0];
                    match node
                    {
                        crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                        { cb, ca, ob, before, oa, after }
                        =>
                          {
                              let child_n_before: usize =
                                  crate::cbordetveraux::append_n_before_sz(cur_off_v, cur_n_v, cb);
                              if child_n_before > 0usize
                              {
                                  let child_off_sz: usize =
                                      crate::cbordetveraux::append_off_before_sz(cur_off_v, ob, cb);
                                  let
                                  ib:
                                  crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                  =
                                      before[0];
                                  (&mut r_node)[0] = ib;
                                  (&mut r_off)[0] = child_off_sz;
                                  (&mut r_n)[0] = child_n_before;
                                  (&mut pcontinue)[0] =
                                      !
                                      crate::cbordetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                          ib
                                      )
                              }
                              else
                              {
                                  let child_off_sz: usize =
                                      crate::cbordetveraux::append_off_after_sz(
                                          cur_off_v,
                                          oa,
                                          ca,
                                          cb
                                      );
                                  let child_n_sz: usize =
                                      crate::cbordetveraux::append_n_after_sz(
                                          cur_off_v,
                                          cur_n_v,
                                          cb
                                      );
                                  let
                                  ia:
                                  crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                  =
                                      after[0];
                                  (&mut r_node)[0] = ia;
                                  (&mut r_off)[0] = child_off_sz;
                                  (&mut r_n)[0] = child_n_sz;
                                  (&mut pcontinue)[0] =
                                      !
                                      crate::cbordetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                          ia
                                      )
                              }
                          },
                        crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                        { .. }
                        => (),
                        _ => panic!("Incomplete pattern matching")
                    }
                };
                let node: crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                    (&r_node)[0];
                let cur_off_v: usize = (&r_off)[0];
                let cur_n_v: usize = (&r_n)[0];
                let
                res:
                (crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                usize)
                =
                    match node
                    {
                        crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                        { _0: bi }
                        =>
                          {
                              let
                              bi·:
                              crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                              =
                                  match bi
                                  {
                                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                      =>
                                        crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                      { sr: s }
                                      =>
                                        if cur_n_v == 0usize
                                        {
                                            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                        }
                                        else
                                        {
                                            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                            { sr: s }
                                        },
                                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                      { ss: s }
                                      =>
                                        {
                                            let
                                            s_pr:
                                            (&[crate::cbordetveraux::cbor_raw],
                                            &[crate::cbordetveraux::cbor_raw])
                                            =
                                                s.split_at(cur_off_v);
                                            let _s_prefix: &[crate::cbordetveraux::cbor_raw] =
                                                s_pr.0;
                                            let s_rest: &[crate::cbordetveraux::cbor_raw] = s_pr.1;
                                            let
                                            s_ms:
                                            (&[crate::cbordetveraux::cbor_raw],
                                            &[crate::cbordetveraux::cbor_raw])
                                            =
                                                s_rest.split_at(cur_n_v);
                                            let s_middle: &[crate::cbordetveraux::cbor_raw] =
                                                s_ms.0;
                                            let _s_suffix: &[crate::cbordetveraux::cbor_raw] =
                                                s_ms.1;
                                            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                            { ss: s_middle }
                                        },
                                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
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
                                                    crate::cbordetveraux::jump_raw_data_item_eta(
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
                                            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                            { count: cur_n_v, payload: pl_suffix }
                                        },
                                      _ => panic!("Incomplete pattern matching")
                                  };
                              let len1: usize =
                                  crate::cbordetveraux::base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                      bi·
                                  );
                              (bi·,len1)
                          },
                        crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                        { .. }
                        => panic!("Pulse.Lib.Dv.unreachable"),
                        _ => panic!("Incomplete pattern matching")
                    };
                let
                bi·: crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                =
                    crate::cbordetveraux::fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                        res
                    );
                let len_sz: usize =
                    crate::cbordetveraux::snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                        res
                    );
                let rest_sz: usize = total_sz.wrapping_sub(len_sz);
                let rest: crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                    match ml
                    {
                        crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                        { _0: bi }
                        =>
                          {
                              let
                              bi·1:
                              crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                              =
                                  match bi
                                  {
                                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                      =>
                                        crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                      { sr: s }
                                      =>
                                        if rest_sz == 0usize
                                        {
                                            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                        }
                                        else
                                        {
                                            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                            { sr: s }
                                        },
                                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                      { ss: s }
                                      =>
                                        {
                                            let
                                            s_pr:
                                            (&[crate::cbordetveraux::cbor_raw],
                                            &[crate::cbordetveraux::cbor_raw])
                                            =
                                                s.split_at(len_sz);
                                            let _s_prefix: &[crate::cbordetveraux::cbor_raw] =
                                                s_pr.0;
                                            let s_rest: &[crate::cbordetveraux::cbor_raw] = s_pr.1;
                                            let
                                            s_ms:
                                            (&[crate::cbordetveraux::cbor_raw],
                                            &[crate::cbordetveraux::cbor_raw])
                                            =
                                                s_rest.split_at(rest_sz);
                                            let s_middle: &[crate::cbordetveraux::cbor_raw] =
                                                s_ms.0;
                                            let _s_suffix: &[crate::cbordetveraux::cbor_raw] =
                                                s_ms.1;
                                            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                            { ss: s_middle }
                                        },
                                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
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
                                                    crate::cbordetveraux::jump_raw_data_item_eta(
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
                                            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                            { count: rest_sz, payload: pl_suffix }
                                        },
                                      _ => panic!("Incomplete pattern matching")
                                  };
                              crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                              { _0: bi·1 }
                          },
                        crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                        { cb, ca, ob, before, oa, after }
                        =>
                          {
                              let cb·_sz: usize =
                                  crate::cbordetveraux::append_n_before_sz(len_sz, rest_sz, cb);
                              let ca·_sz: usize =
                                  crate::cbordetveraux::append_n_after_sz(len_sz, rest_sz, cb);
                              let ob·_sz: usize =
                                  crate::cbordetveraux::append_off_before_sz(len_sz, ob, cb);
                              let oa·_sz: usize =
                                  crate::cbordetveraux::append_off_after_sz(len_sz, oa, ca, cb);
                              crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                              { cb: cb·_sz, ca: ca·_sz, ob: ob·_sz, before, oa: oa·_sz, after }
                          },
                        _ => panic!("Incomplete pattern matching")
                    };
                crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IPair
                { before: bi·, after: rest }
            };
        let it0: crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw = it;
        let mut pit: [crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw; 1] =
            [it0; 1usize];
        let mut pj: [u64; 1] = [0u64; 1usize];
        let cont0: bool = 0u64 < i;
        let mut pcont: [bool; 1] = [cont0; 1usize];
        while
        (&pcont)[0]
        {
            let i_cur: crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                (&pit)[0];
            let
            _letpattern:
            (crate::cbordetveraux::cbor_raw,
            crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw)
            =
                crate::cbordetveraux::iterator_next_raw_data_item(i_cur);
            let elem: crate::cbordetveraux::cbor_raw =
                {
                    let res: crate::cbordetveraux::cbor_raw = _letpattern.0;
                    let
                    it·: crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                    =
                        _letpattern.1;
                    (&mut pit)[0] = it·;
                    res
                };
            crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(elem);
            let j_val: u64 = (&pj)[0];
            (&mut pj)[0] = j_val.wrapping_add(1u64);
            let new_cont: bool = j_val.wrapping_add(1u64) < i;
            (&mut pcont)[0] = new_cont
        };
        let i_cur: crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
            (&pit)[0];
        let
        _letpattern:
        (crate::cbordetveraux::cbor_raw,
        crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw)
        =
            crate::cbordetveraux::iterator_next_raw_data_item(i_cur);
        let res: crate::cbordetveraux::cbor_raw =
            {
                let res: crate::cbordetveraux::cbor_raw = _letpattern.0;
                let it·: crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                    _letpattern.1;
                (&mut pit)[0] = it·;
                res
            };
        option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Some { v: res }
    }
}

pub fn cbor_det_map_length(x: crate::cbordetveraux::cbor_raw) -> u64
{ crate::cbordetveraux::cbor_raw_read_map_length(x) }

pub type cbor_det_map_iterator_t <'a> =
crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
<'a>;

pub fn cbor_det_map_iterator_start <'a>(x: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    let
    ml:
    crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    =
        crate::cbordetveraux::cbor_raw_get_map(x);
    let total_sz: usize =
        crate::cbordetveraux::mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
            ml
        );
    if total_sz == 0usize
    {
        crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IBase
        {
            before:
            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
        }
    }
    else
    {
        let
        mut
        r_node:
        [crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;
        1]
        =
            [ml; 1usize];
        let mut r_off: [usize; 1] = [0usize; 1usize];
        let mut r_n: [usize; 1] = [total_sz; 1usize];
        let mut pcontinue: [bool; 1] =
            [!
                crate::cbordetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                    ml
                );
                1usize];
        while
        (&pcontinue)[0]
        {
            let
            node:
            crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            =
                (&r_node)[0];
            let cur_off_v: usize = (&r_off)[0];
            let cur_n_v: usize = (&r_n)[0];
            match node
            {
                crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                { cb, ca, ob, before, oa, after }
                =>
                  {
                      let child_n_before: usize =
                          crate::cbordetveraux::append_n_before_sz(cur_off_v, cur_n_v, cb);
                      if child_n_before > 0usize
                      {
                          let child_off_sz: usize =
                              crate::cbordetveraux::append_off_before_sz(cur_off_v, ob, cb);
                          let
                          ib:
                          crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                          =
                              before[0];
                          (&mut r_node)[0] = ib;
                          (&mut r_off)[0] = child_off_sz;
                          (&mut r_n)[0] = child_n_before;
                          (&mut pcontinue)[0] =
                              !
                              crate::cbordetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                  ib
                              )
                      }
                      else
                      {
                          let child_off_sz: usize =
                              crate::cbordetveraux::append_off_after_sz(cur_off_v, oa, ca, cb);
                          let child_n_sz: usize =
                              crate::cbordetveraux::append_n_after_sz(cur_off_v, cur_n_v, cb);
                          let
                          ia:
                          crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                          =
                              after[0];
                          (&mut r_node)[0] = ia;
                          (&mut r_off)[0] = child_off_sz;
                          (&mut r_n)[0] = child_n_sz;
                          (&mut pcontinue)[0] =
                              !
                              crate::cbordetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                  ia
                              )
                      }
                  },
                crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                { .. }
                => (),
                _ => panic!("Incomplete pattern matching")
            }
        };
        let
        node:
        crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        =
            (&r_node)[0];
        let cur_off_v: usize = (&r_off)[0];
        let cur_n_v: usize = (&r_n)[0];
        let
        res:
        (crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
        usize)
        =
            match node
            {
                crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                { _0: bi }
                =>
                  {
                      let
                      bi·:
                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                      =
                          match bi
                          {
                              crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                              =>
                                crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                              crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                              { sr: s }
                              =>
                                if cur_n_v == 0usize
                                {
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                }
                                else
                                {
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                    { sr: s }
                                },
                              crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                              { ss: s }
                              =>
                                {
                                    let
                                    s_pr:
                                    (&[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                    &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                    =
                                        s.split_at(cur_off_v);
                                    let
                                    _s_prefix:
                                    &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                    =
                                        s_pr.0;
                                    let
                                    s_rest:
                                    &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                    =
                                        s_pr.1;
                                    let
                                    s_ms:
                                    (&[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                    &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                    =
                                        s_rest.split_at(cur_n_v);
                                    let
                                    s_middle:
                                    &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                    =
                                        s_ms.0;
                                    let
                                    _s_suffix:
                                    &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                    =
                                        s_ms.1;
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                    { ss: s_middle }
                                },
                              crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
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
                                            crate::cbordetveraux::jump_nondep_then_raw_data_item_eta(
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
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                    { count: cur_n_v, payload: pl_suffix }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      let len: usize =
                          crate::cbordetveraux::base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                              bi·
                          );
                      (bi·,len)
                  },
                crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                { .. }
                => panic!("Pulse.Lib.Dv.unreachable"),
                _ => panic!("Incomplete pattern matching")
            };
        let
        bi·:
        crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        =
            crate::cbordetveraux::fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                res
            );
        let len_sz: usize =
            crate::cbordetveraux::snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                res
            );
        let rest_sz: usize = total_sz.wrapping_sub(len_sz);
        let
        rest:
        crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        =
            match ml
            {
                crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                { _0: bi }
                =>
                  {
                      let
                      bi·1:
                      crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                      =
                          match bi
                          {
                              crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                              =>
                                crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                              crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                              { sr: s }
                              =>
                                if rest_sz == 0usize
                                {
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                }
                                else
                                {
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                    { sr: s }
                                },
                              crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                              { ss: s }
                              =>
                                {
                                    let
                                    s_pr:
                                    (&[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                    &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                    =
                                        s.split_at(len_sz);
                                    let
                                    _s_prefix:
                                    &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                    =
                                        s_pr.0;
                                    let
                                    s_rest:
                                    &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                    =
                                        s_pr.1;
                                    let
                                    s_ms:
                                    (&[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                    &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                    =
                                        s_rest.split_at(rest_sz);
                                    let
                                    s_middle:
                                    &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                    =
                                        s_ms.0;
                                    let
                                    _s_suffix:
                                    &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                    =
                                        s_ms.1;
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                    { ss: s_middle }
                                },
                              crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
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
                                            crate::cbordetveraux::jump_nondep_then_raw_data_item_eta(
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
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                    { count: rest_sz, payload: pl_suffix }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                      { _0: bi·1 }
                  },
                crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                { cb, ca, ob, before, oa, after }
                =>
                  {
                      let cb·_sz: usize =
                          crate::cbordetveraux::append_n_before_sz(len_sz, rest_sz, cb);
                      let ca·_sz: usize =
                          crate::cbordetveraux::append_n_after_sz(len_sz, rest_sz, cb);
                      let ob·_sz: usize =
                          crate::cbordetveraux::append_off_before_sz(len_sz, ob, cb);
                      let oa·_sz: usize =
                          crate::cbordetveraux::append_off_after_sz(len_sz, oa, ca, cb);
                      crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                      { cb: cb·_sz, ca: ca·_sz, ob: ob·_sz, before, oa: oa·_sz, after }
                  },
                _ => panic!("Incomplete pattern matching")
            };
        crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IPair
        { before: bi·, after: rest }
    }
}

pub fn cbor_det_map_iterator_is_empty(
    x:
    crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
) ->
    bool
{
    match x
    {
        crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IBase
        { before: bi }
        =>
          {
              let len_before: usize =
                  crate::cbordetveraux::base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                      bi
                  );
              len_before == 0usize
          },
        crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IPair
        { before: bi, .. }
        =>
          {
              let len_before: usize =
                  crate::cbordetveraux::base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                      bi
                  );
              len_before == 0usize
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn cbor_det_map_iterator_next <'a>(
    x:
    crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
) ->
    (crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>,
    crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>)
{
    let
    mut
    r:
    [crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;
    1]
    =
        [x; 1usize];
    let
    i_cur:
    crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    =
        (&r)[0];
    let
    _letpattern:
    (crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
    crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw)
    =
        crate::cbordetveraux::iterator_next_map_entry_raw_data_item(i_cur);
    let elt: crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
        {
            let res: crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                _letpattern.0;
            let
            it·:
            crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            =
                _letpattern.1;
            (&mut r)[0] = it·;
            res
        };
    let
    x·:
    crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    =
        (&r)[0];
    (elt,x·)
}

pub fn cbor_det_map_entry_key <'a>(
    x2: crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>
) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x2.cbor_map_entry_key }

pub fn cbor_det_map_entry_value <'a>(
    x2: crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>
) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x2.cbor_map_entry_value }

pub fn cbor_det_map_get <'a>(
    x: crate::cbordetveraux::cbor_raw <'a>,
    k: crate::cbordetveraux::cbor_raw <'a>
) ->
    option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    let
    ml:
    crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    =
        crate::cbordetveraux::cbor_raw_get_map(x);
    let total_sz: usize =
        crate::cbordetveraux::mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
            ml
        );
    let
    it:
    crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    =
        if total_sz == 0usize
        {
            crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IBase
            {
                before:
                crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
            }
        }
        else
        {
            let
            mut
            r_node:
            [crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;
            1]
            =
                [ml; 1usize];
            let mut r_off: [usize; 1] = [0usize; 1usize];
            let mut r_n: [usize; 1] = [total_sz; 1usize];
            let mut pcontinue: [bool; 1] =
                [!
                    crate::cbordetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                        ml
                    );
                    1usize];
            while
            (&pcontinue)[0]
            {
                let
                node:
                crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                =
                    (&r_node)[0];
                let cur_off_v: usize = (&r_off)[0];
                let cur_n_v: usize = (&r_n)[0];
                match node
                {
                    crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                    { cb, ca, ob, before, oa, after }
                    =>
                      {
                          let child_n_before: usize =
                              crate::cbordetveraux::append_n_before_sz(cur_off_v, cur_n_v, cb);
                          if child_n_before > 0usize
                          {
                              let child_off_sz: usize =
                                  crate::cbordetveraux::append_off_before_sz(cur_off_v, ob, cb);
                              let
                              ib:
                              crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                              =
                                  before[0];
                              (&mut r_node)[0] = ib;
                              (&mut r_off)[0] = child_off_sz;
                              (&mut r_n)[0] = child_n_before;
                              (&mut pcontinue)[0] =
                                  !
                                  crate::cbordetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                      ib
                                  )
                          }
                          else
                          {
                              let child_off_sz: usize =
                                  crate::cbordetveraux::append_off_after_sz(cur_off_v, oa, ca, cb);
                              let child_n_sz: usize =
                                  crate::cbordetveraux::append_n_after_sz(cur_off_v, cur_n_v, cb);
                              let
                              ia:
                              crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                              =
                                  after[0];
                              (&mut r_node)[0] = ia;
                              (&mut r_off)[0] = child_off_sz;
                              (&mut r_n)[0] = child_n_sz;
                              (&mut pcontinue)[0] =
                                  !
                                  crate::cbordetveraux::uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                      ia
                                  )
                          }
                      },
                    crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                    { .. }
                    => (),
                    _ => panic!("Incomplete pattern matching")
                }
            };
            let
            node:
            crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            =
                (&r_node)[0];
            let cur_off_v: usize = (&r_off)[0];
            let cur_n_v: usize = (&r_n)[0];
            let
            res:
            (crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
            usize)
            =
                match node
                {
                    crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                    { _0: bi }
                    =>
                      {
                          let
                          bi·:
                          crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                          =
                              match bi
                              {
                                  crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                  =>
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                  crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                  { sr: s }
                                  =>
                                    if cur_n_v == 0usize
                                    {
                                        crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                    }
                                    else
                                    {
                                        crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                        { sr: s }
                                    },
                                  crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                  { ss: s }
                                  =>
                                    {
                                        let
                                        s_pr:
                                        (&[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                        &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                        =
                                            s.split_at(cur_off_v);
                                        let
                                        _s_prefix:
                                        &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                        =
                                            s_pr.0;
                                        let
                                        s_rest:
                                        &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                        =
                                            s_pr.1;
                                        let
                                        s_ms:
                                        (&[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                        &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                        =
                                            s_rest.split_at(cur_n_v);
                                        let
                                        s_middle:
                                        &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                        =
                                            s_ms.0;
                                        let
                                        _s_suffix:
                                        &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                        =
                                            s_ms.1;
                                        crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                        { ss: s_middle }
                                    },
                                  crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
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
                                                crate::cbordetveraux::jump_nondep_then_raw_data_item_eta(
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
                                        crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                        { count: cur_n_v, payload: pl_suffix }
                                    },
                                  _ => panic!("Incomplete pattern matching")
                              };
                          let len: usize =
                              crate::cbordetveraux::base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                  bi·
                              );
                          (bi·,len)
                      },
                    crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                    { .. }
                    => panic!("Pulse.Lib.Dv.unreachable"),
                    _ => panic!("Incomplete pattern matching")
                };
            let
            bi·:
            crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            =
                crate::cbordetveraux::fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                    res
                );
            let len_sz: usize =
                crate::cbordetveraux::snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                    res
                );
            let rest_sz: usize = total_sz.wrapping_sub(len_sz);
            let
            rest:
            crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            =
                match ml
                {
                    crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                    { _0: bi }
                    =>
                      {
                          let
                          bi·1:
                          crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                          =
                              match bi
                              {
                                  crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                  =>
                                    crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                  crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                  { sr: s }
                                  =>
                                    if rest_sz == 0usize
                                    {
                                        crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                    }
                                    else
                                    {
                                        crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                        { sr: s }
                                    },
                                  crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                  { ss: s }
                                  =>
                                    {
                                        let
                                        s_pr:
                                        (&[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                        &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                        =
                                            s.split_at(len_sz);
                                        let
                                        _s_prefix:
                                        &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                        =
                                            s_pr.0;
                                        let
                                        s_rest:
                                        &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                        =
                                            s_pr.1;
                                        let
                                        s_ms:
                                        (&[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                        &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                        =
                                            s_rest.split_at(rest_sz);
                                        let
                                        s_middle:
                                        &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                        =
                                            s_ms.0;
                                        let
                                        _s_suffix:
                                        &[crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                        =
                                            s_ms.1;
                                        crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                        { ss: s_middle }
                                    },
                                  crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
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
                                                crate::cbordetveraux::jump_nondep_then_raw_data_item_eta(
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
                                        crate::cbordetveraux::base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                        { count: rest_sz, payload: pl_suffix }
                                    },
                                  _ => panic!("Incomplete pattern matching")
                              };
                          crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                          { _0: bi·1 }
                      },
                    crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                    { cb, ca, ob, before, oa, after }
                    =>
                      {
                          let cb·_sz: usize =
                              crate::cbordetveraux::append_n_before_sz(len_sz, rest_sz, cb);
                          let ca·_sz: usize =
                              crate::cbordetveraux::append_n_after_sz(len_sz, rest_sz, cb);
                          let ob·_sz: usize =
                              crate::cbordetveraux::append_off_before_sz(len_sz, ob, cb);
                          let oa·_sz: usize =
                              crate::cbordetveraux::append_off_after_sz(len_sz, oa, ca, cb);
                          crate::cbordetveraux::mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                          { cb: cb·_sz, ca: ca·_sz, ob: ob·_sz, before, oa: oa·_sz, after }
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IPair
            { before: bi·, after: rest }
        };
    let
    it0:
    crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    =
        it;
    let
    mut
    pit:
    [crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;
    1]
    =
        [it0; 1usize];
    let mut pres: [option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw; 1] =
        [option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::None; 1usize];
    let is_empty: bool =
        match it0
        {
            crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IBase
            { before: bi }
            =>
              {
                  let len_before: usize =
                      crate::cbordetveraux::base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                          bi
                      );
                  len_before == 0usize
              },
            crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IPair
            { before: bi, .. }
            =>
              {
                  let len_before: usize =
                      crate::cbordetveraux::base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                          bi
                      );
                  len_before == 0usize
              },
            _ => panic!("Incomplete pattern matching")
        };
    let cont0: bool = ! is_empty;
    let mut pcont: [bool; 1] = [cont0; 1usize];
    while
    (&pcont)[0]
    {
        let
        i_cur:
        crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        =
            (&pit)[0];
        let
        _letpattern:
        (crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
        crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw)
        =
            crate::cbordetveraux::iterator_next_map_entry_raw_data_item(i_cur);
        let entry: crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
            {
                let
                res: crate::cbordetveraux::cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                =
                    _letpattern.0;
                let
                it·:
                crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                =
                    _letpattern.1;
                (&mut pit)[0] = it·;
                res
            };
        let key: crate::cbordetveraux::cbor_raw = entry.cbor_map_entry_key;
        let comp: i16 = crate::cbordetveraux::impl_cbor_compare(key, k);
        let eq: bool = comp == 0i16;
        if eq
        {
            let value: crate::cbordetveraux::cbor_raw = entry.cbor_map_entry_value;
            (&mut pres)[0] = option__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Some { v: value };
            (&mut pcont)[0] = false
        }
        else
        {
            let
            i·:
            crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            =
                (&pit)[0];
            let is_empty·: bool =
                match i·
                {
                    crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IBase
                    { before: bi }
                    =>
                      {
                          let len_before: usize =
                              crate::cbordetveraux::base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                  bi
                              );
                          len_before == 0usize
                      },
                    crate::cbordetveraux::iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::IPair
                    { before: bi, .. }
                    =>
                      {
                          let len_before: usize =
                              crate::cbordetveraux::base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                  bi
                              );
                          len_before == 0usize
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            let cont·: bool = ! is_empty·;
            (&mut pcont)[0] = cont·
        }
    };
    (&pres)[0]
}

pub fn cbor_det_serialize_string(ty: u8, off: u64, out: &mut [u8]) -> usize
{
    let off·: crate::cbordetveraux::raw_uint64 = crate::cbordetveraux::mk_raw_uint64(off);
    crate::cbordetveraux::cbor_serialize_string(ty, off·, out)
}

pub fn cbor_det_serialize_tag(tag: u64, output: &mut [u8]) -> usize
{
    let tag·: crate::cbordetveraux::raw_uint64 = crate::cbordetveraux::mk_raw_uint64(tag);
    crate::cbordetveraux::cbor_serialize_tag(tag·, output)
}

pub fn cbor_det_serialize_array(len: u64, out: &mut [u8], off: usize) -> usize
{
    let len·: crate::cbordetveraux::raw_uint64 = crate::cbordetveraux::mk_raw_uint64(len);
    crate::cbordetveraux::cbor_serialize_array(len·, out, off)
}

pub fn cbor_det_serialize_map_insert(out: &mut [u8], off2: usize, off3: usize) -> bool
{ crate::cbordetveraux::cbor_raw_map_insert(out, off2, off3) }

pub fn cbor_det_serialize_map(len: u64, out: &mut [u8], off: usize) -> usize
{
    let len·: crate::cbordetveraux::raw_uint64 = crate::cbordetveraux::mk_raw_uint64(len);
    crate::cbordetveraux::cbor_serialize_map(len·, out, off)
}

pub fn dummy_cbor_det_t <'a>() -> crate::cbordetveraux::cbor_raw <'a>
{ crate::cbordetveraux::cbor_raw::CBOR_Case_Simple { v: 0u8 } }
