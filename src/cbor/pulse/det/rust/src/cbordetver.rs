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
    let res: usize = crate::cbordetveraux::cbor_validate_det(input);
    let len: usize = res;
    if len == 0usize
    { option__·CBOR_Pulse_Raw_Type_cbor_raw···size_t·::None }
    else
    {
        let res0: crate::cbordetveraux::cbor_raw = crate::cbordetveraux::cbor_parse(input, len);
        let res1: crate::cbordetveraux::cbor_raw = res0;
        option__·CBOR_Pulse_Raw_Type_cbor_raw···size_t·::Some { v: (res1,len) }
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
        let res: usize = crate::cbordetveraux::cbor_serialize(x, out);
        let len·: usize = res;
        option__size_t::Some { v: len· }
    }
    else
    { option__size_t::None }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__CBOR_Pulse_Raw_Type_cbor_raw <'a>
{
    None,
    Some { v: crate::cbordetveraux::cbor_raw <'a> }
}

pub fn cbor_det_mk_simple_value <'a>(v: u8) -> option__CBOR_Pulse_Raw_Type_cbor_raw <'a>
{
    if
    v <= crate::cbordetveraux::max_simple_value_additional_info
    ||
    crate::cbordetveraux::min_simple_value_long_argument <= v
    {
        let res: crate::cbordetveraux::cbor_raw = crate::cbordetveraux::cbor_det_mk_simple_value(v);
        option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res }
    }
    else
    { option__CBOR_Pulse_Raw_Type_cbor_raw::None }
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
    option__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{
    if s.len() > 18446744073709551615u64 as usize
    { option__CBOR_Pulse_Raw_Type_cbor_raw::None }
    else
    {
        let len64: crate::cbordetveraux::raw_uint64 =
            crate::cbordetveraux::mk_raw_uint64(s.len() as u64);
        let ite: u8 =
            if ty == cbor_det_string_kind::ByteString
            { crate::cbordetveraux::cbor_major_type_byte_string }
            else
            { crate::cbordetveraux::cbor_major_type_text_string };
        let ress: crate::cbordetveraux::cbor_string =
            crate::cbordetveraux::cbor_string
            { cbor_string_type: ite, cbor_string_size: len64.size, cbor_string_ptr: s };
        let res: crate::cbordetveraux::cbor_raw =
            crate::cbordetveraux::cbor_raw::CBOR_Case_String { v: ress };
        option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res }
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
    option__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{
    if a.len() > 18446744073709551615u64 as usize
    { option__CBOR_Pulse_Raw_Type_cbor_raw::None }
    else
    {
        let len64: crate::cbordetveraux::raw_uint64 =
            crate::cbordetveraux::mk_raw_uint64(a.len() as u64);
        let res·: crate::cbordetveraux::cbor_array =
            crate::cbordetveraux::cbor_array
            { cbor_array_length_size: len64.size, cbor_array_ptr: a };
        let res: crate::cbordetveraux::cbor_raw =
            crate::cbordetveraux::cbor_raw::CBOR_Case_Array { v: res· };
        option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res }
    }
}

pub fn cbor_det_mk_map <'a>(a: &'a mut [crate::cbordetveraux::cbor_map_entry <'a>]) ->
    option__CBOR_Pulse_Raw_Type_cbor_raw
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
                let raw_len: crate::cbordetveraux::raw_uint64 =
                    crate::cbordetveraux::mk_raw_uint64(a.len() as u64);
                let res·: crate::cbordetveraux::cbor_map =
                    crate::cbordetveraux::cbor_map
                    { cbor_map_length_size: raw_len.size, cbor_map_ptr: a };
                let res: crate::cbordetveraux::cbor_raw =
                    crate::cbordetveraux::cbor_raw::CBOR_Case_Map { v: res· };
                (&mut dest)[0] = res;
                true
            }
            else
            { false }
        };
    if bres
    {
        let res: crate::cbordetveraux::cbor_raw = (&dest)[0];
        option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res }
    }
    else
    { option__CBOR_Pulse_Raw_Type_cbor_raw::None }
}

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
        let _letpattern: crate::cbordetveraux::cbor_raw = c;
        let s: &[u8] =
            match _letpattern
            {
                crate::cbordetveraux::cbor_raw::CBOR_Case_String { v: c· } => c·.cbor_string_ptr,
                _ => panic!("Incomplete pattern matching")
            };
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
    option__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{
    let len: u64 = cbor_det_get_array_length(x);
    if i >= len
    { option__CBOR_Pulse_Raw_Type_cbor_raw::None }
    else
    {
        let res: crate::cbordetveraux::cbor_raw =
            crate::cbordetveraux::cbor_det_get_array_item(x, i);
        option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res }
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
    option__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{
    let mut dest: [crate::cbordetveraux::cbor_raw; 1] = [k; 1usize];
    let res: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
        crate::cbordetveraux::cbor_map_iterator_init(x);
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry = res;
    let mut pi: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry; 1] =
        [i; 1usize];
    let mut pres: [option__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [option__CBOR_Pulse_Raw_Type_cbor_raw::None; 1usize];
    let i_is_empty: bool = crate::cbordetveraux::cbor_det_map_iterator_is_empty(i);
    let cont: bool = ! i_is_empty;
    let mut pcont: [bool; 1] = [cont; 1usize];
    while
    (&pcont)[0]
    {
        let entry: crate::cbordetveraux::cbor_map_entry =
            crate::cbordetveraux::cbor_det_map_iterator_next(&mut pi);
        let key: crate::cbordetveraux::cbor_raw =
            crate::cbordetveraux::cbor_det_map_entry_key(entry);
        let comp: i16 = crate::cbordetveraux::impl_cbor_det_compare(key, k);
        if comp == 0i16
        {
            let value: crate::cbordetveraux::cbor_raw =
                crate::cbordetveraux::cbor_det_map_entry_value(entry);
            (&mut pres)[0] = option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: value };
            (&mut pcont)[0] = false
        }
        else if comp > 0i16
        { (&mut pcont)[0] = false }
        else
        {
            let i·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
                (&pi)[0];
            let is_empty: bool = crate::cbordetveraux::cbor_det_map_iterator_is_empty(i·);
            let cont1: bool = ! is_empty;
            (&mut pcont)[0] = cont1
        }
    };
    let res0: option__CBOR_Pulse_Raw_Type_cbor_raw = (&pres)[0];
    let _bind_c: bool =
        match res0
        {
            option__CBOR_Pulse_Raw_Type_cbor_raw::None => false,
            option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: vres } =>
              {
                  (&mut dest)[0] = vres;
                  true
              },
            _ => panic!("Incomplete pattern matching")
        };
    let bres: bool = _bind_c;
    if bres
    {
        let res1: crate::cbordetveraux::cbor_raw = (&dest)[0];
        option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res1 }
    }
    else
    { option__CBOR_Pulse_Raw_Type_cbor_raw::None }
}
