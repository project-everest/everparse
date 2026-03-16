#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub type cbornondet <'a> = crate::cbornondetveraux::cbor_raw <'a>;

pub fn cbor_nondet_reset_perm <'a>(c: crate::cbornondetveraux::cbor_raw <'a>) ->
    crate::cbornondetveraux::cbor_raw
    <'a>
{ crate::cbornondetveraux::cbor_raw_reset_perm_tot(c) }

pub fn cbor_nondet_parse <'a>(
    map_key_bound: crate::cbornondetveraux::option__size_t,
    strict_check: bool,
    input: &'a [u8]
) ->
    crate::cbornondetveraux::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{ crate::cbornondetveraux::cbor_nondet_parse(map_key_bound, strict_check, input) }

pub fn cbor_nondet_size(x: crate::cbornondetveraux::cbor_raw, bound: usize) -> usize
{ crate::cbornondetveraux::cbor_nondet_size(x, bound) }

pub fn cbor_nondet_serialize(x: crate::cbornondetveraux::cbor_raw, output: &mut [u8]) ->
    crate::cbornondetveraux::option__size_t
{ crate::cbornondetveraux::cbor_nondet_serialize(x, output) }

pub fn cbor_nondet_mk_simple_value <'a>(v: u8) ->
    crate::cbornondetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{
    if
    v <= crate::cbornondetveraux::max_simple_value_additional_info
    ||
    crate::cbornondetveraux::min_simple_value_long_argument <= v
    {
        let res: crate::cbornondetveraux::cbor_raw =
            crate::cbornondetveraux::cbor_nondet_mk_simple_value(v);
        crate::cbornondetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res }
    }
    else
    { crate::cbornondetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw::None }
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
    crate::cbornondetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{
    if s.len() > 18446744073709551615u64 as usize
    { crate::cbornondetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw::None }
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
            let res: crate::cbornondetveraux::cbor_raw =
                crate::cbornondetveraux::cbor_nondet_mk_string(ite, s);
            crate::cbornondetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res }
        }
        else
        { crate::cbornondetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw::None }
    }
}

pub fn cbor_nondet_mk_tagged <'a>(tag: u64, r: &'a [crate::cbornondetveraux::cbor_raw <'a>]) ->
    crate::cbornondetveraux::cbor_raw
    <'a>
{ crate::cbornondetveraux::cbor_nondet_mk_tagged(tag, r) }

pub type cbor_nondet_map_entry <'a> = crate::cbornondetveraux::cbor_map_entry <'a>;

pub fn cbor_nondet_mk_map_entry <'a>(
    xk: crate::cbornondetveraux::cbor_raw <'a>,
    xv: crate::cbornondetveraux::cbor_raw <'a>
) ->
    crate::cbornondetveraux::cbor_map_entry
    <'a>
{ crate::cbornondetveraux::cbor_nondet_mk_map_entry(xk, xv) }

pub fn cbor_nondet_mk_array <'a>(a: &'a [crate::cbornondetveraux::cbor_raw <'a>]) ->
    crate::cbornondetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{
    if a.len() > 18446744073709551615u64 as usize
    { crate::cbornondetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw::None }
    else
    {
        let res: crate::cbornondetveraux::cbor_raw =
            crate::cbornondetveraux::cbor_nondet_mk_array(a);
        crate::cbornondetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res }
    }
}

pub fn cbor_nondet_mk_map <'a>(a: &'a [crate::cbornondetveraux::cbor_map_entry <'a>]) ->
    crate::cbornondetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{ crate::cbornondetveraux::cbor_nondet_mk_map(a) }

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
    let ty: u8 = cbor_nondet_major_type(c);
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
        let i: u64 = crate::cbornondetveraux::cbor_nondet_read_uint64(c);
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
        let s: &[u8] = crate::cbornondetveraux::cbor_nondet_get_string(c);
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
        let tag: u64 = crate::cbornondetveraux::cbor_nondet_get_tagged_tag(c);
        let payload: crate::cbornondetveraux::cbor_raw =
            crate::cbornondetveraux::cbor_nondet_get_tagged_payload(c);
        cbor_nondet_view::Tagged { tag, payload }
    }
    else
    {
        let i: u8 = crate::cbornondetveraux::cbor_nondet_read_simple_value(c);
        cbor_nondet_view::SimpleValue { _0: i }
    }
}

pub fn cbor_nondet_get_array_length(x: crate::cbornondetveraux::cbor_raw) -> u64
{ crate::cbornondetveraux::cbor_nondet_get_array_length(x) }

pub type cbor_nondet_array_iterator_t <'a> =
crate::cbornondetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>;

pub fn cbor_nondet_array_iterator_start <'a>(x: crate::cbornondetveraux::cbor_raw <'a>) ->
    crate::cbornondetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{ crate::cbornondetveraux::cbor_nondet_array_iterator_start(x) }

pub fn cbor_nondet_array_iterator_is_empty(
    x: crate::cbornondetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
) ->
    bool
{ crate::cbornondetveraux::cbor_nondet_array_iterator_is_empty(x) }

pub fn cbor_nondet_array_iterator_next <'b, 'a>(
    x: &'b mut [crate::cbornondetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>]
) ->
    crate::cbornondetveraux::cbor_raw
    <'a>
{ crate::cbornondetveraux::cbor_nondet_array_iterator_next(x) }

pub fn cbor_nondet_array_iterator_length(
    x: crate::cbornondetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
) ->
    u64
{ crate::cbornondetveraux::cbor_array_iterator_length(x) }

pub fn cbor_nondet_array_iterator_truncate <'a>(
    x: crate::cbornondetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>,
    len: u64
) ->
    crate::cbornondetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{ crate::cbornondetveraux::cbor_array_iterator_truncate(x, len) }

pub fn cbor_nondet_get_array_item <'a>(x: crate::cbornondetveraux::cbor_raw <'a>, i: u64) ->
    crate::cbornondetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{
    let len: u64 = cbor_nondet_get_array_length(x);
    if i >= len
    { crate::cbornondetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw::None }
    else
    {
        let res: crate::cbornondetveraux::cbor_raw =
            crate::cbornondetveraux::cbor_nondet_get_array_item(x, i);
        crate::cbornondetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res }
    }
}

pub fn cbor_nondet_map_length(x: crate::cbornondetveraux::cbor_raw) -> u64
{ crate::cbornondetveraux::cbor_nondet_get_map_length(x) }

pub type cbor_nondet_map_iterator_t <'a> =
crate::cbornondetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>;

pub fn cbor_nondet_map_iterator_start <'a>(x: crate::cbornondetveraux::cbor_raw <'a>) ->
    crate::cbornondetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
    <'a>
{ crate::cbornondetveraux::cbor_nondet_map_iterator_start(x) }

pub fn cbor_nondet_map_iterator_is_empty(
    x: crate::cbornondetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
) ->
    bool
{ crate::cbornondetveraux::cbor_nondet_map_iterator_is_empty(x) }

pub fn cbor_nondet_map_iterator_next <'b, 'a>(
    x:
    &'b mut [crate::cbornondetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>]
) ->
    crate::cbornondetveraux::cbor_map_entry
    <'a>
{ crate::cbornondetveraux::cbor_nondet_map_iterator_next(x) }

pub fn cbor_nondet_map_entry_key <'a>(x2: crate::cbornondetveraux::cbor_map_entry <'a>) ->
    crate::cbornondetveraux::cbor_raw
    <'a>
{ crate::cbornondetveraux::cbor_nondet_map_entry_key(x2) }

pub fn cbor_nondet_map_entry_value <'a>(x2: crate::cbornondetveraux::cbor_map_entry <'a>) ->
    crate::cbornondetveraux::cbor_raw
    <'a>
{ crate::cbornondetveraux::cbor_nondet_map_entry_value(x2) }

pub fn cbor_nondet_map_get <'a>(
    x: crate::cbornondetveraux::cbor_raw <'a>,
    k: crate::cbornondetveraux::cbor_raw <'a>
) ->
    crate::cbornondetveraux::option__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{ crate::cbornondetveraux::cbor_nondet_map_get(x, k) }

pub fn dummy_cbor_nondet_t <'a>() -> crate::cbornondetveraux::cbor_raw <'a>
{ crate::cbornondetveraux::cbor_raw::CBOR_Case_Simple { v: 0u8 } }
