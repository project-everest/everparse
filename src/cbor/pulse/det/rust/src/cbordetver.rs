#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub type cbordet <'a> = crate::cbordetveraux::cbor_raw <'a>;

#[derive(PartialEq, Clone, Copy)]
pub enum option__·CBOR_Pulse_Raw_Type_cbor_raw···size_t· <'a>
{
    None,
    Some { v: (crate::cbordetveraux::cbor_raw <'a>, usize) }
}

pub fn cbor_det_parse <'a>(input: &'a [u8]) ->
    option__·CBOR_Pulse_Raw_Type_cbor_raw···size_t·
    <'a>
{
    let len: usize = crate::cbordetveraux::cbor_det_validate(input);
    if len == 0usize
    { option__·CBOR_Pulse_Raw_Type_cbor_raw···size_t·::None }
    else
    {
        let res: crate::cbordetveraux::cbor_raw = crate::cbordetveraux::cbor_det_parse(input, len);
        option__·CBOR_Pulse_Raw_Type_cbor_raw···size_t·::Some { v: (res,len) }
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__size_t
{
    None,
    Some { v: usize }
}

pub fn cbor_det_size <'a>(x: crate::cbordetveraux::cbor_raw <'a>, bound: usize) ->
    option__size_t
{
    let size: usize = crate::cbordetveraux::cbor_det_size(x, bound);
    if size == 0usize { option__size_t::None } else { option__size_t::Some { v: size } }
}

pub fn cbor_det_serialize <'a>(x: crate::cbordetveraux::cbor_raw <'a>, output: &'a mut [u8]) ->
    option__size_t
{
    let len: usize = crate::cbordetveraux::cbor_det_size(x, output.len());
    if len > 0usize
    {
        let _letpattern: (&mut [u8], &mut [u8]) = output.split_at_mut(len);
        let out: &mut [u8] = _letpattern.0;
        let _rem: &[u8] = _letpattern.1;
        let len·: usize = crate::cbordetveraux::cbor_det_serialize(x, out);
        option__size_t::Some { v: len· }
    }
    else
    { option__size_t::None }
}

pub fn cbor_det_mk_simple_value <'a>(v: u8) ->
    crate::cbordetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{
    if
    v <= crate::cbordetveraux::max_simple_value_additional_info
    ||
    crate::cbordetveraux::min_simple_value_long_argument <= v
    {
        let res: crate::cbordetveraux::cbor_raw = crate::cbordetveraux::cbor_det_mk_simple_value(v);
        crate::cbordetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res }
    }
    else
    { crate::cbordetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw::None }
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
    crate::cbordetveraux::cbor_det_mk_int64(ite, v)
}

#[derive(PartialEq, Clone, Copy)]
pub enum cbor_det_string_kind
{
    ByteString,
    TextString
}

pub fn cbor_det_mk_string <'a>(ty: cbor_det_string_kind, s: &'a [u8]) ->
    crate::cbordetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{
    if s.len() > 18446744073709551615u64 as usize
    { crate::cbordetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw::None }
    else
    {
        let ite: u8 =
            if ty == cbor_det_string_kind::ByteString
            { crate::cbordetveraux::cbor_major_type_byte_string }
            else
            { crate::cbordetveraux::cbor_major_type_text_string };
        let res: crate::cbordetveraux::cbor_raw = crate::cbordetveraux::cbor_det_mk_string(ite, s);
        crate::cbordetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res }
    }
}

pub fn cbor_det_mk_tagged <'a>(tag: u64, r: &'a [crate::cbordetveraux::cbor_raw <'a>]) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ crate::cbordetveraux::cbor_det_mk_tagged(tag, r) }

pub type cbor_det_map_entry <'a> = crate::cbordetveraux::cbor_map_entry <'a>;

pub fn cbor_det_mk_map_entry <'a>(
    xk: crate::cbordetveraux::cbor_raw <'a>,
    xv: crate::cbordetveraux::cbor_raw <'a>
) ->
    crate::cbordetveraux::cbor_map_entry
    <'a>
{ crate::cbordetveraux::cbor_det_mk_map_entry(xk, xv) }

pub fn cbor_det_mk_array <'a>(a: &'a [crate::cbordetveraux::cbor_raw <'a>]) ->
    crate::cbordetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{
    if a.len() > 18446744073709551615u64 as usize
    { crate::cbordetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw::None }
    else
    {
        let res: crate::cbordetveraux::cbor_raw = crate::cbordetveraux::cbor_det_mk_array(a);
        crate::cbordetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res }
    }
}

pub fn cbor_det_mk_map <'a>(a: &'a mut [crate::cbordetveraux::cbor_map_entry <'a>]) ->
    crate::cbordetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{ crate::cbordetveraux::cbor_det_mk_map_gen(a) }

pub fn cbor_det_equal <'a>(
    x1: crate::cbordetveraux::cbor_raw <'a>,
    x2: crate::cbordetveraux::cbor_raw <'a>
) ->
    bool
{ crate::cbordetveraux::cbor_det_equal(x1, x2) }

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
    let ty: u8 = crate::cbordetveraux::cbor_det_major_type(c);
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
        let i: u64 = crate::cbordetveraux::cbor_det_read_uint64(c);
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
        let s: &[u8] = crate::cbordetveraux::cbor_det_get_string(c);
        cbor_det_view::String { kind: k, payload: s }
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
        let tag: u64 = crate::cbordetveraux::cbor_det_get_tagged_tag(c);
        let payload: crate::cbordetveraux::cbor_raw =
            crate::cbordetveraux::cbor_det_get_tagged_payload(c);
        cbor_det_view::Tagged { tag, payload }
    }
    else
    {
        let i: u8 = crate::cbordetveraux::cbor_det_read_simple_value(c);
        cbor_det_view::SimpleValue { _0: i }
    }
}

pub fn cbor_det_get_array_length <'a>(x: crate::cbordetveraux::cbor_raw <'a>) -> u64
{
    let res: u64 = crate::cbordetveraux::cbor_det_get_array_length(x);
    res
}

pub type cbor_det_array_iterator_t <'a> =
crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>;

pub fn cbor_det_array_iterator_start <'a>(x: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{
    let res: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetveraux::cbor_det_array_iterator_start(x);
    res
}

pub fn cbor_det_array_iterator_is_empty <'a>(
    x: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>
) ->
    bool
{ crate::cbordetveraux::cbor_det_array_iterator_is_empty(x) }

pub fn cbor_det_array_iterator_next <'b, 'a>(
    x: &'b mut [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>]
) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ crate::cbordetveraux::cbor_det_array_iterator_next(x) }

pub fn cbor_det_get_array_item <'a>(x: crate::cbordetveraux::cbor_raw <'a>, i: u64) ->
    crate::cbordetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{
    let len: u64 = cbor_det_get_array_length(x);
    if i >= len
    { crate::cbordetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw::None }
    else
    {
        let res: crate::cbordetveraux::cbor_raw =
            crate::cbordetveraux::cbor_det_get_array_item(x, i);
        crate::cbordetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res }
    }
}

pub fn cbor_det_map_length <'a>(x: crate::cbordetveraux::cbor_raw <'a>) -> u64
{
    let res: u64 = crate::cbordetveraux::cbor_det_get_map_length(x);
    res
}

pub type cbor_det_map_iterator_t <'a> =
crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>;

pub fn cbor_det_map_iterator_start <'a>(x: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
    <'a>
{
    let res: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
        crate::cbordetveraux::cbor_det_map_iterator_start(x);
    res
}

pub fn cbor_det_map_iterator_is_empty <'a>(
    x: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>
) ->
    bool
{ crate::cbordetveraux::cbor_det_map_iterator_is_empty(x) }

pub fn cbor_det_map_iterator_next <'b, 'a>(
    x: &'b mut [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>]
) ->
    crate::cbordetveraux::cbor_map_entry
    <'a>
{ crate::cbordetveraux::cbor_det_map_iterator_next(x) }

pub fn cbor_det_map_entry_key <'a>(x2: crate::cbordetveraux::cbor_map_entry <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ crate::cbordetveraux::cbor_det_map_entry_key(x2) }

pub fn cbor_det_map_entry_value <'a>(x2: crate::cbordetveraux::cbor_map_entry <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ crate::cbordetveraux::cbor_det_map_entry_value(x2) }

pub fn cbor_det_map_get <'a>(
    x: crate::cbordetveraux::cbor_raw <'a>,
    k: crate::cbordetveraux::cbor_raw <'a>
) ->
    crate::cbordetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{
    let res: crate::cbordetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetveraux::cbor_det_map_get(x, k);
    res
}
