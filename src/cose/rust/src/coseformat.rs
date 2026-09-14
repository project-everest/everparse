#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub type evercddl_uint = u64;

pub type nint = u64;

#[derive(PartialEq, Clone, Copy)]
enum evercddl_int_tags
{
    Mkevercddl_int0,
    Mkevercddl_int1
}

#[derive(PartialEq, Clone, Copy)]
pub enum evercddl_int
{
    Mkevercddl_int0 { _x0: u64 },
    Mkevercddl_int1 { _x0: u64 }
}

#[derive(PartialEq, Clone, Copy)]
enum evercddl_label_tags
{
    Mkevercddl_label0,
    Mkevercddl_label1
}

#[derive(PartialEq, Clone, Copy)]
pub enum evercddl_label <'a>
{
    Mkevercddl_label0 { _x0: evercddl_int },
    Mkevercddl_label1 { _x0: &'a [u8] }
}

pub type aux_env34_type_1 <'a> = evercddl_label <'a>;

pub type any <'a> = crate::cbordetveraux::cbor_raw <'a>;

pub type values <'a> = crate::cbordetveraux::cbor_raw <'a>;

#[derive(PartialEq, Clone, Copy)]
pub enum either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t_tags
{
    Inl,
    Inr
}

#[derive(PartialEq, Clone, Copy)]
pub enum either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t <'a>
{
    Inl { v: evercddl_int },
    Inr { v: &'a [u8] }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__FStar_Pervasives_either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t
<'a>
{
    None,
    Some { v: either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t <'a> }
}

#[derive(PartialEq, Clone, Copy)]
pub struct
array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
<'a>
{
    pub cddl_array_iterator_contents:
    crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>,
    pub cddl_array_iterator_impl_validate:
    fn (&mut [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw]) -> bool,
    pub cddl_array_iterator_impl_parse:
    for<'a1>
    fn
    (crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a1>)
    ->
    evercddl_label
    <'a1>
}

#[derive(PartialEq, Clone, Copy)]
pub enum
either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
<'a>
{
    Inl { v: &'a [evercddl_label <'a>] },
    Inr
    {
        v:
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
        <'a>
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
<'a>
{
    None,
    Some
    {
        v:
        either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
        <'a>
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int <'a>
{
    Inl { v: &'a [u8] },
    Inr { v: evercddl_int }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int
<'a>
{
    None,
    Some { v: either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int <'a> }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__Pulse_Lib_Slice_slice·uint8_t <'a>
{
    None,
    Some { v: &'a [u8] }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···
<'a>
{
    Inl
    {
        v:
        (&'a [u8],
        crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags)
    },
    Inr
    {
        v:
        (crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags,
        crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags)
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_FStar_Pervasives_either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···
<'a>
{
    Inl
    {
        v:
        (&'a [u8],
        crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags)
    },
    Inr
    {
        v:
        either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···
        <'a>
    }
}

#[derive(PartialEq, Clone, Copy)]
pub struct
map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
<'a>
{
    pub cddl_map_iterator_contents:
    crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>,
    pub cddl_map_iterator_impl_validate1: fn (crate::cbordetveraux::cbor_raw) -> bool,
    pub cddl_map_iterator_impl_parse1:
    for<'a1> fn (crate::cbordetveraux::cbor_raw <'a1>) -> evercddl_label <'a1>,
    pub cddl_map_iterator_impl_validate_ex: fn (crate::cbordetveraux::cbor_map_entry) -> bool,
    pub cddl_map_iterator_impl_validate2: fn (crate::cbordetveraux::cbor_raw) -> bool,
    pub cddl_map_iterator_impl_parse2:
    for<'a1> fn (crate::cbordetveraux::cbor_raw <'a1>) -> crate::cbordetveraux::cbor_raw <'a1>
}

#[derive(PartialEq, Clone, Copy)]
pub enum
either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
<'a>
{
    Inl { v: &'a [(evercddl_label <'a>, crate::cbordetveraux::cbor_raw <'a>)] },
    Inr
    {
        v:
        map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
        <'a>
    }
}

#[derive(PartialEq, Clone, Copy)]
pub struct header_map <'a>
{
    pub intkey1:
    option__FStar_Pervasives_either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t <'a>,
    pub intkey2:
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
    <'a>,
    pub intkey3:
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int <'a>,
    pub intkey4: option__Pulse_Lib_Slice_slice·uint8_t <'a>,
    pub _x0:
    either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_FStar_Pervasives_either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···
    <'a>,
    pub _x1:
    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
}

#[derive(PartialEq, Clone, Copy)]
enum empty_or_serialized_map_tags
{
    Mkempty_or_serialized_map0,
    Mkempty_or_serialized_map1
}

#[derive(PartialEq, Clone, Copy)]
pub enum empty_or_serialized_map <'a>
{
    Mkempty_or_serialized_map0 { _x0: header_map <'a> },
    Mkempty_or_serialized_map1 { _x0: &'a [u8] }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
either__·COSE_Format_empty_or_serialized_map····Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t··_·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    Inl { v: (empty_or_serialized_map <'a>, (&'a [u8], &'a [u8])) },
    Inr { v: (&'a [u8], &'a [u8]) }
}

#[derive(PartialEq, Clone, Copy)]
pub struct sig_structure <'a>
{
    pub context: either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t_tags,
    pub body_protected: empty_or_serialized_map <'a>,
    pub _x0:
    either__·COSE_Format_empty_or_serialized_map····Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t··_·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
}

pub fn sig_structure_left <'a>(x8: sig_structure <'a>) ->
    (either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t_tags,
    (empty_or_serialized_map
    <'a>,
    either__·COSE_Format_empty_or_serialized_map····Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t··_·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·
    <'a>))
{ (x8.context,(x8.body_protected,x8._x0)) }

#[derive(PartialEq, Clone, Copy)]
pub enum empty_or_serialized_map_ugly <'a>
{
    Inl { v: header_map <'a> },
    Inr { v: &'a [u8] }
}

pub fn empty_or_serialized_map_left <'a>(x8: empty_or_serialized_map <'a>) ->
    empty_or_serialized_map_ugly
    <'a>
{
    match x8
    {
        empty_or_serialized_map::Mkempty_or_serialized_map0 { _x0: x10 } =>
          empty_or_serialized_map_ugly::Inl { v: x10 },
        empty_or_serialized_map::Mkempty_or_serialized_map1 { _x0: x12 } =>
          empty_or_serialized_map_ugly::Inr { v: x12 },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn header_map_left <'a>(x14: header_map <'a>) ->
    (((((option__FStar_Pervasives_either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t
    <'a>,
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
    <'a>),
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int
    <'a>),
    option__Pulse_Lib_Slice_slice·uint8_t
    <'a>),
    either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_FStar_Pervasives_either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···
    <'a>),
    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
    <'a>)
{ (((((x14.intkey1,x14.intkey2),x14.intkey3),x14.intkey4),x14._x0),x14._x1) }

#[derive(PartialEq, Clone, Copy)]
pub enum evercddl_int_ugly
{
    Inl { v: u64 },
    Inr { v: u64 }
}

pub fn evercddl_int_left(x8: evercddl_int) -> evercddl_int_ugly
{
    match x8
    {
        evercddl_int::Mkevercddl_int0 { _x0: x10 } => evercddl_int_ugly::Inl { v: x10 },
        evercddl_int::Mkevercddl_int1 { _x0: x12 } => evercddl_int_ugly::Inr { v: x12 },
        _ => panic!("Incomplete pattern matching")
    }
}

pub type evercddl_uint_ugly = u64;

pub fn evercddl_uint_left(x4: u64) -> u64 { x4 }

/**
Serializer for evercddl_uint
*/
pub fn
serialize_uint(c: u64, out: &mut [u8]) ->
    usize
{
    let mty: crate::cbordetver::cbor_det_int_kind = crate::cbordetver::cbor_det_int_kind::UInt64;
    let x: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty, c);
    let ser: crate::cbordetver::option__size_t = crate::cbordetver::cbor_det_serialize(x, out);
    match ser
    {
        crate::cbordetver::option__size_t::None => 0usize,
        crate::cbordetver::option__size_t::Some { v: sz } => sz,
        _ => panic!("Incomplete pattern matching")
    }
}

pub type nint_ugly = u64;

pub fn nint_left(x4: u64) -> u64 { x4 }

/**
Serializer for nint
*/
pub fn
serialize_nint(c: u64, out: &mut [u8]) ->
    usize
{
    let mty: crate::cbordetver::cbor_det_int_kind =
        if
        crate::cbordetveraux::cbor_major_type_neg_int64
        ==
        crate::cbordetveraux::cbor_major_type_uint64
        { crate::cbordetver::cbor_det_int_kind::UInt64 }
        else
        { crate::cbordetver::cbor_det_int_kind::NegInt64 };
    let x: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty, c);
    let ser: crate::cbordetver::option__size_t = crate::cbordetver::cbor_det_serialize(x, out);
    match ser
    {
        crate::cbordetver::option__size_t::None => 0usize,
        crate::cbordetver::option__size_t::Some { v: sz } => sz,
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Serializer for evercddl_int
*/
pub fn
serialize_int(c: evercddl_int, out: &mut [u8]) ->
    usize
{
    match evercddl_int_left(c)
    {
        evercddl_int_ugly::Inl { v: c1 } => serialize_uint(c1, out),
        evercddl_int_ugly::Inr { v: c2 } => serialize_nint(c2, out),
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn tstr_left <'a>(x4: &'a [u8]) -> &'a [u8] { x4 }

/**
Serializer for tstr
*/
pub fn
serialize_tstr(c: &[u8], out: &mut [u8]) ->
    usize
{
    let len: usize = c.len();
    let __anf0: bool = crate::cbordetveraux::sizet_lte_u64(len, 18446744073709551615u64);
    if __anf0
    {
        let correct: bool = crate::cbordetver::cbor_impl_utf8_correct(c);
        if correct
        {
            let mty: crate::cbordetver::cbor_det_string_kind =
                if
                crate::cbordetveraux::cbor_major_type_text_string
                ==
                crate::cbordetveraux::cbor_major_type_byte_string
                { crate::cbordetver::cbor_det_string_kind::ByteString }
                else
                { crate::cbordetver::cbor_det_string_kind::TextString };
            let res: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                crate::cbordetver::cbor_det_mk_string(mty, c);
            let x: crate::cbordetveraux::cbor_raw =
                match res
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: c1 } => c1,
                    _ => panic!("Incomplete pattern matching")
                };
            let ser: crate::cbordetver::option__size_t =
                crate::cbordetver::cbor_det_serialize(x, out);
            match ser
            {
                crate::cbordetver::option__size_t::None => 0usize,
                crate::cbordetver::option__size_t::Some { v: sz } => sz,
                _ => panic!("Incomplete pattern matching")
            }
        }
        else
        { 0usize }
    }
    else
    { 0usize }
}

pub type evercddl_label_ugly <'a> =
either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t <'a>;

pub fn evercddl_label_left <'a>(x8: evercddl_label <'a>) ->
    either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t
    <'a>
{
    match x8
    {
        evercddl_label::Mkevercddl_label0 { _x0: x10 } =>
          either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t::Inl { v: x10 },
        evercddl_label::Mkevercddl_label1 { _x0: x12 } =>
          either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t::Inr { v: x12 },
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Serializer for evercddl_label
*/
pub fn
serialize_evercddl_label(c: evercddl_label, out: &mut [u8]) ->
    usize
{
    match evercddl_label_left(c)
    {
        either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t::Inl { v: c1 } =>
          serialize_int(c1, out),
        either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t::Inr { v: c2 } =>
          serialize_tstr(c2, out),
        _ => panic!("Incomplete pattern matching")
    }
}

pub type aux_env34_type_1_ugly <'a> = evercddl_label <'a>;

pub fn aux_env34_type_1_left <'a>(x4: evercddl_label <'a>) -> evercddl_label <'a> { x4 }

/**
Serializer for aux_env34_type_1
*/
pub fn
aux_env34_serialize_1(
    c: evercddl_label,
    out: &mut [u8],
    out_count: &mut [u64],
    out_size: &mut [usize]
) ->
    bool
{
    let count: u64 = out_count[0usize];
    if count < 18446744073709551615u64
    {
        let size: usize = out_size[0usize];
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
        let _out0: &[u8] = _letpattern.0;
        let out1: &mut [u8] = _letpattern.1;
        let size1: usize = serialize_evercddl_label(c, out1);
        if size1 == 0usize
        { false }
        else
        {
            out_count[0usize] = count.wrapping_add(1u64);
            out_size[0usize] = size.wrapping_add(size1);
            true
        }
    }
    else
    { false }
}

pub fn bstr_left <'a>(x4: &'a [u8]) -> &'a [u8] { x4 }

/**
Serializer for bstr
*/
pub fn
serialize_bstr(c: &[u8], out: &mut [u8]) ->
    usize
{
    let len: usize = c.len();
    let __anf0: bool = crate::cbordetveraux::sizet_lte_u64(len, 18446744073709551615u64);
    if __anf0
    {
        let mty: crate::cbordetver::cbor_det_string_kind =
            crate::cbordetver::cbor_det_string_kind::ByteString;
        let res: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
            crate::cbordetver::cbor_det_mk_string(mty, c);
        let x: crate::cbordetveraux::cbor_raw =
            match res
            {
                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: c1 } => c1,
                _ => panic!("Incomplete pattern matching")
            };
        let ser: crate::cbordetver::option__size_t = crate::cbordetver::cbor_det_serialize(x, out);
        match ser
        {
            crate::cbordetver::option__size_t::None => 0usize,
            crate::cbordetver::option__size_t::Some { v: sz } => sz,
            _ => panic!("Incomplete pattern matching")
        }
    }
    else
    { 0usize }
}

/**
Serializer for everparsenomatch
*/
pub fn
serialize_everparsenomatch(out: &[u8]) ->
    usize
{
    crate::lowstar::ignore::ignore::<&[u8]>(out);
    0usize
}

pub type any_ugly <'a> = crate::cbordetveraux::cbor_raw <'a>;

pub fn any_left <'a>(x4: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x4 }

/**
Serializer for any
*/
pub fn
serialize_any(c: crate::cbordetveraux::cbor_raw, out: &mut [u8]) ->
    usize
{
    let ser: crate::cbordetver::option__size_t = crate::cbordetver::cbor_det_serialize(c, out);
    match ser
    {
        crate::cbordetver::option__size_t::None => 0usize,
        crate::cbordetver::option__size_t::Some { v: sz } => sz,
        _ => panic!("Incomplete pattern matching")
    }
}

pub type values_ugly <'a> = crate::cbordetveraux::cbor_raw <'a>;

pub fn values_left <'a>(x4: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x4 }

/**
Serializer for values
*/
pub fn
serialize_values(c: crate::cbordetveraux::cbor_raw, out: &mut [u8]) ->
    usize
{ serialize_any(c, out) }

pub fn validate_uint(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    mt == crate::cbordetveraux::cbor_major_type_uint64
}

pub fn validate_nint(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    mt == crate::cbordetveraux::cbor_major_type_neg_int64
}

pub fn validate_int(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let test: bool = validate_uint(c);
    if test { true } else { validate_nint(c) }
}

pub fn validate_tstr(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    mt == crate::cbordetveraux::cbor_major_type_text_string
}

pub fn validate_evercddl_label(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let test: bool = validate_int(c);
    if test { true } else { validate_tstr(c) }
}

pub fn validate_bstr(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    mt == crate::cbordetveraux::cbor_major_type_byte_string
}

pub fn aux_env34_map_constraint_2(x: crate::cbordetveraux::cbor_map_entry) -> bool
{
    let k: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
    let mt: u8 = crate::cbordetver::cbor_det_major_type(k);
    let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;
    let testk: bool =
        if is_uint
        {
            let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(k);
            let i: u64 =
                match v
                {
                    crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                    _ => panic!("Incomplete pattern matching")
                };
            i == 1u64
        }
        else
        { false };
    let test: bool =
        if testk
        {
            let v: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_value(x);
            let test: bool = validate_int(v);
            if test { true } else { validate_tstr(v) }
        }
        else
        { false };
    let test1: bool =
        if test
        { true }
        else
        {
            let k1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
            let mt1: u8 = crate::cbordetver::cbor_det_major_type(k1);
            let is_uint1: bool = mt1 == crate::cbordetveraux::cbor_major_type_uint64;
            let testk1: bool =
                if is_uint1
                {
                    let v: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(k1);
                    let i: u64 =
                        match v
                        {
                            crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                            _ => panic!("Incomplete pattern matching")
                        };
                    i == 2u64
                }
                else
                { false };
            if testk1
            {
                let v: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_map_entry_value(x);
                let ty: u8 = crate::cbordetver::cbor_det_major_type(v);
                if ty == crate::cbordetveraux::cbor_major_type_array
                {
                    let v1: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(v);
                    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                        match v1
                        {
                            crate::cbordetver::cbor_det_view::Array { _0: a } =>
                              crate::cbordetver::cbor_det_array_iterator_start(a),
                            _ => panic!("Incomplete pattern matching")
                        };
                    let
                    mut
                    pi:
                    [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
                    =
                        [i; 1usize];
                    let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                        (&pi)[0usize];
                    let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
                    let test1: bool =
                        if is_done
                        { false }
                        else
                        {
                            let c: crate::cbordetveraux::cbor_raw =
                                crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                            validate_evercddl_label(c)
                        };
                    let b_success: bool =
                        if test1
                        {
                            let mut pcont: [bool; 1] = [true; 1usize];
                            while
                            (&pcont)[0usize]
                            {
                                let
                                i11:
                                crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                =
                                    (&pi)[0usize];
                                let
                                i2:
                                crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                =
                                    (&pi)[0usize];
                                let is_done1: bool =
                                    crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
                                let cont: bool =
                                    if is_done1
                                    { false }
                                    else
                                    {
                                        let c: crate::cbordetveraux::cbor_raw =
                                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                        validate_evercddl_label(c)
                                    };
                                if ! cont
                                {
                                    (&mut pi)[0usize] = i11;
                                    (&mut pcont)[0usize] = false
                                }
                            };
                            true
                        }
                        else
                        { false };
                    if b_success
                    {
                        let
                        i·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                        =
                            (&pi)[0usize];
                        crate::cbordetver::cbor_det_array_iterator_is_empty(i·)
                    }
                    else
                    { false }
                }
                else
                { false }
            }
            else
            { false }
        };
    let test2: bool =
        if test1
        { true }
        else
        {
            let k1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
            let mt1: u8 = crate::cbordetver::cbor_det_major_type(k1);
            let is_uint1: bool = mt1 == crate::cbordetveraux::cbor_major_type_uint64;
            let testk1: bool =
                if is_uint1
                {
                    let v: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(k1);
                    let i: u64 =
                        match v
                        {
                            crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                            _ => panic!("Incomplete pattern matching")
                        };
                    i == 3u64
                }
                else
                { false };
            if testk1
            {
                let v: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_map_entry_value(x);
                let test2: bool = validate_tstr(v);
                if test2 { true } else { validate_int(v) }
            }
            else
            { false }
        };
    let test3: bool =
        if test2
        { true }
        else
        {
            let k1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
            let mt1: u8 = crate::cbordetver::cbor_det_major_type(k1);
            let is_uint1: bool = mt1 == crate::cbordetveraux::cbor_major_type_uint64;
            let testk1: bool =
                if is_uint1
                {
                    let v: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(k1);
                    let i: u64 =
                        match v
                        {
                            crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                            _ => panic!("Incomplete pattern matching")
                        };
                    i == 4u64
                }
                else
                { false };
            if testk1
            {
                let v: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_map_entry_value(x);
                validate_bstr(v)
            }
            else
            { false }
        };
    let test4: bool =
        if test3
        { true }
        else
        {
            let k1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
            let mt1: u8 = crate::cbordetver::cbor_det_major_type(k1);
            let is_uint1: bool = mt1 == crate::cbordetveraux::cbor_major_type_uint64;
            let testk1: bool =
                if is_uint1
                {
                    let v: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(k1);
                    let i: u64 =
                        match v
                        {
                            crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                            _ => panic!("Incomplete pattern matching")
                        };
                    i == 5u64
                }
                else
                { false };
            if testk1
            {
                let discarded: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_map_entry_value(x);
                crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(discarded);
                true
            }
            else
            { false }
        };
    if test4
    { true }
    else
    {
        let k1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
        let mt1: u8 = crate::cbordetver::cbor_det_major_type(k1);
        let is_uint1: bool = mt1 == crate::cbordetveraux::cbor_major_type_uint64;
        let testk1: bool =
            if is_uint1
            {
                let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(k1);
                let i: u64 =
                    match v
                    {
                        crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                        _ => panic!("Incomplete pattern matching")
                    };
                i == 6u64
            }
            else
            { false };
        if testk1
        {
            let discarded: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_map_entry_value(x);
            crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(discarded);
            true
        }
        else
        { false }
    }
}

/**
Serializer for header_map
*/
pub fn
serialize_header_map(c: header_map, out: &mut [u8]) ->
    usize
{
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let
    _letpattern:
    (((((option__FStar_Pervasives_either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t,
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label),
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int),
    option__Pulse_Lib_Slice_slice·uint8_t),
    either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_FStar_Pervasives_either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···),
    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw)
    =
        header_map_left(c);
    let res: bool =
        {
            let
            c1:
            ((((option__FStar_Pervasives_either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t,
            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label),
            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int),
            option__Pulse_Lib_Slice_slice·uint8_t),
            either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_FStar_Pervasives_either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···)
            =
                _letpattern.0;
            let
            c2:
            either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
            =
                _letpattern.1;
            let res1: bool =
                {
                    let
                    c11:
                    (((option__FStar_Pervasives_either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t,
                    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label),
                    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int),
                    option__Pulse_Lib_Slice_slice·uint8_t)
                    =
                        c1.0;
                    let
                    c21:
                    either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_FStar_Pervasives_either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···
                    =
                        c1.1;
                    let res1: bool =
                        {
                            let
                            c12:
                            ((option__FStar_Pervasives_either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t,
                            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label),
                            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int)
                            =
                                c11.0;
                            let c22: option__Pulse_Lib_Slice_slice·uint8_t = c11.1;
                            let res1: bool =
                                {
                                    let
                                    c13:
                                    (option__FStar_Pervasives_either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t,
                                    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label)
                                    =
                                        c12.0;
                                    let
                                    c23:
                                    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int
                                    =
                                        c12.1;
                                    let res1: bool =
                                        {
                                            let
                                            c14:
                                            option__FStar_Pervasives_either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t
                                            =
                                                c13.0;
                                            let
                                            c24:
                                            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
                                            =
                                                c13.1;
                                            let res1: bool =
                                                match c14
                                                {
                                                    option__FStar_Pervasives_either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t::Some
                                                    { v: c15 }
                                                    =>
                                                      {
                                                          let count: u64 = (&pcount)[0usize];
                                                          if count < 18446744073709551615u64
                                                          {
                                                              let size0: usize = (&psize)[0usize];
                                                              let
                                                              _letpattern1: (&mut [u8], &mut [u8])
                                                              =
                                                                  out.split_at_mut(size0);
                                                              let _out0: &[u8] = _letpattern1.0;
                                                              let out1: &mut [u8] = _letpattern1.1;
                                                              let
                                                              mty:
                                                              crate::cbordetver::cbor_det_int_kind
                                                              =
                                                                  crate::cbordetver::cbor_det_int_kind::UInt64;
                                                              let
                                                              c3: crate::cbordetveraux::cbor_raw
                                                              =
                                                                  crate::cbordetver::cbor_det_mk_int64(
                                                                      mty,
                                                                      1u64
                                                                  );
                                                              let
                                                              res: crate::cbordetver::option__size_t
                                                              =
                                                                  crate::cbordetver::cbor_det_serialize(
                                                                      c3,
                                                                      out1
                                                                  );
                                                              let res1: usize =
                                                                  match res
                                                                  {
                                                                      crate::cbordetver::option__size_t::None
                                                                      => 0usize,
                                                                      crate::cbordetver::option__size_t::Some
                                                                      { v: r }
                                                                      => r,
                                                                      _ =>
                                                                        panic!(
                                                                            "Incomplete pattern matching"
                                                                        )
                                                                  };
                                                              if res1 > 0usize
                                                              {
                                                                  let size1: usize =
                                                                      size0.wrapping_add(res1);
                                                                  let
                                                                  _letpattern2:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size1);
                                                                  let _out01: &[u8] =
                                                                      _letpattern2.0;
                                                                  let out2: &mut [u8] =
                                                                      _letpattern2.1;
                                                                  let res2: usize =
                                                                      match c15
                                                                      {
                                                                          either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t::Inl
                                                                          { v: c16 }
                                                                          =>
                                                                            serialize_int(c16, out2),
                                                                          either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t::Inr
                                                                          { v: c25 }
                                                                          =>
                                                                            serialize_tstr(
                                                                                c25,
                                                                                out2
                                                                            ),
                                                                          _ =>
                                                                            panic!(
                                                                                "Incomplete pattern matching"
                                                                            )
                                                                      };
                                                                  if res2 > 0usize
                                                                  {
                                                                      let size2: usize =
                                                                          size1.wrapping_add(res2);
                                                                      let
                                                                      _letpattern3:
                                                                      (&mut [u8], &mut [u8])
                                                                      =
                                                                          out.split_at_mut(size2);
                                                                      let out012: &mut [u8] =
                                                                          _letpattern3.0;
                                                                      let _out_rest: &[u8] =
                                                                          _letpattern3.1;
                                                                      let res3: bool =
                                                                          crate::cbordetver::cbor_det_serialize_map_insert(
                                                                              out012,
                                                                              size0,
                                                                              size1
                                                                          );
                                                                      if res3
                                                                      {
                                                                          (&mut psize)[0usize] =
                                                                              size2;
                                                                          (&mut pcount)[0usize] =
                                                                              count.wrapping_add(
                                                                                  1u64
                                                                              );
                                                                          true
                                                                      }
                                                                      else
                                                                      { false }
                                                                  }
                                                                  else
                                                                  { false }
                                                              }
                                                              else
                                                              { false }
                                                          }
                                                          else
                                                          { false }
                                                      },
                                                    option__FStar_Pervasives_either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t::None
                                                    => true,
                                                    _ => panic!("Incomplete pattern matching")
                                                };
                                            if res1
                                            {
                                                match c24
                                                {
                                                    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label::Some
                                                    { v: c15 }
                                                    =>
                                                      {
                                                          let count: u64 = (&pcount)[0usize];
                                                          if count < 18446744073709551615u64
                                                          {
                                                              let size0: usize = (&psize)[0usize];
                                                              let
                                                              _letpattern1: (&mut [u8], &mut [u8])
                                                              =
                                                                  out.split_at_mut(size0);
                                                              let _out0: &[u8] = _letpattern1.0;
                                                              let out1: &mut [u8] = _letpattern1.1;
                                                              let
                                                              mty:
                                                              crate::cbordetver::cbor_det_int_kind
                                                              =
                                                                  crate::cbordetver::cbor_det_int_kind::UInt64;
                                                              let
                                                              c3: crate::cbordetveraux::cbor_raw
                                                              =
                                                                  crate::cbordetver::cbor_det_mk_int64(
                                                                      mty,
                                                                      2u64
                                                                  );
                                                              let
                                                              res: crate::cbordetver::option__size_t
                                                              =
                                                                  crate::cbordetver::cbor_det_serialize(
                                                                      c3,
                                                                      out1
                                                                  );
                                                              let res11: usize =
                                                                  match res
                                                                  {
                                                                      crate::cbordetver::option__size_t::None
                                                                      => 0usize,
                                                                      crate::cbordetver::option__size_t::Some
                                                                      { v: r }
                                                                      => r,
                                                                      _ =>
                                                                        panic!(
                                                                            "Incomplete pattern matching"
                                                                        )
                                                                  };
                                                              if res11 > 0usize
                                                              {
                                                                  let size1: usize =
                                                                      size0.wrapping_add(res11);
                                                                  let
                                                                  _letpattern2:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size1);
                                                                  let _out01: &[u8] =
                                                                      _letpattern2.0;
                                                                  let out2: &mut [u8] =
                                                                      _letpattern2.1;
                                                                  let mut pcount1: [u64; 1] =
                                                                      [0u64; 1usize];
                                                                  let mut psize1: [usize; 1] =
                                                                      [0usize; 1usize];
                                                                  let res2: bool =
                                                                      match c15
                                                                      {
                                                                          either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label::Inl
                                                                          { v: c16 }
                                                                          =>
                                                                            if c16.len() == 0usize
                                                                            { false }
                                                                            else
                                                                            {
                                                                                let
                                                                                mut pres: [bool; 1]
                                                                                =
                                                                                    [true; 1usize];
                                                                                let
                                                                                mut pi: [usize; 1]
                                                                                =
                                                                                    [0usize; 1usize];
                                                                                let slen: usize =
                                                                                    c16.len();
                                                                                let res2: bool =
                                                                                    (&pres)[0usize];
                                                                                let i: usize =
                                                                                    (&pi)[0usize];
                                                                                let mut cond: bool =
                                                                                    res2 && i < slen;
                                                                                while
                                                                                cond
                                                                                {
                                                                                    let i0: usize =
                                                                                        (&pi)[0usize];
                                                                                    let
                                                                                    x:
                                                                                    evercddl_label
                                                                                    =
                                                                                        c16[i0];
                                                                                    let
                                                                                    res20: bool
                                                                                    =
                                                                                        aux_env34_serialize_1(
                                                                                            x,
                                                                                            out2,
                                                                                            &mut
                                                                                            pcount1,
                                                                                            &mut
                                                                                            psize1
                                                                                        );
                                                                                    if res20
                                                                                    {
                                                                                        let
                                                                                        i·: usize
                                                                                        =
                                                                                            i0.wrapping_add(
                                                                                                1usize
                                                                                            );
                                                                                        (&mut pi)[0usize] =
                                                                                            i·
                                                                                    }
                                                                                    else
                                                                                    {
                                                                                        (&mut pres)[0usize] =
                                                                                            false
                                                                                    };
                                                                                    let
                                                                                    res21: bool
                                                                                    =
                                                                                        (&pres)[0usize];
                                                                                    let i1: usize =
                                                                                        (&pi)[0usize];
                                                                                    cond =
                                                                                        res21
                                                                                        &&
                                                                                        i1 < slen
                                                                                };
                                                                                (&pres)[0usize]
                                                                            },
                                                                          either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label::Inr
                                                                          { v: c25 }
                                                                          =>
                                                                            {
                                                                                let em: bool =
                                                                                    crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                                                        c25.cddl_array_iterator_contents
                                                                                    );
                                                                                if em
                                                                                { false }
                                                                                else
                                                                                {
                                                                                    let
                                                                                    mut
                                                                                    pc:
                                                                                    [array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label;
                                                                                    1]
                                                                                    =
                                                                                        [c25;
                                                                                            1usize];
                                                                                    let
                                                                                    mut
                                                                                    pres:
                                                                                    [bool; 1]
                                                                                    =
                                                                                        [true;
                                                                                            1usize];
                                                                                    let
                                                                                    c4:
                                                                                    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
                                                                                    =
                                                                                        (&pc)[0usize];
                                                                                    let em1: bool =
                                                                                        crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                                                            c4.cddl_array_iterator_contents
                                                                                        );
                                                                                    let res2: bool =
                                                                                        (&pres)[0usize];
                                                                                    let
                                                                                    mut cond: bool
                                                                                    =
                                                                                        res2
                                                                                        &&
                                                                                        ! em1;
                                                                                    while
                                                                                    cond
                                                                                    {
                                                                                        let
                                                                                        i:
                                                                                        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
                                                                                        =
                                                                                            (&pc)[0usize];
                                                                                        let
                                                                                        len0: u64
                                                                                        =
                                                                                            crate::cbordetver::cbor_det_array_iterator_length(
                                                                                                i.cddl_array_iterator_contents
                                                                                            );
                                                                                        let
                                                                                        mut
                                                                                        pj:
                                                                                        [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw;
                                                                                        1]
                                                                                        =
                                                                                            [i.cddl_array_iterator_contents;
                                                                                                1usize];
                                                                                        let
                                                                                        discarded:
                                                                                        bool
                                                                                        =
                                                                                            (i.cddl_array_iterator_impl_validate)(
                                                                                                &mut
                                                                                                pj
                                                                                            );
                                                                                        crate::lowstar::ignore::ignore::<bool>(
                                                                                            discarded
                                                                                        );
                                                                                        let
                                                                                        ji:
                                                                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                                                        =
                                                                                            (&pj)[0usize];
                                                                                        let
                                                                                        len1: u64
                                                                                        =
                                                                                            crate::cbordetver::cbor_det_array_iterator_length(
                                                                                                ji
                                                                                            );
                                                                                        let
                                                                                        j:
                                                                                        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
                                                                                        =
                                                                                            array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
                                                                                            {
                                                                                                cddl_array_iterator_contents:
                                                                                                ji,
                                                                                                cddl_array_iterator_impl_validate:
                                                                                                i.cddl_array_iterator_impl_validate,
                                                                                                cddl_array_iterator_impl_parse:
                                                                                                i.cddl_array_iterator_impl_parse
                                                                                            };
                                                                                        (&mut pc)[0usize] =
                                                                                            j;
                                                                                        let
                                                                                        tri:
                                                                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                                                        =
                                                                                            crate::cbordetver::cbor_det_array_iterator_truncate(
                                                                                                i.cddl_array_iterator_contents,
                                                                                                len0.wrapping_sub(
                                                                                                    len1
                                                                                                )
                                                                                            );
                                                                                        let
                                                                                        x:
                                                                                        evercddl_label
                                                                                        =
                                                                                            (i.cddl_array_iterator_impl_parse)(
                                                                                                tri
                                                                                            );
                                                                                        let
                                                                                        res20: bool
                                                                                        =
                                                                                            aux_env34_serialize_1(
                                                                                                x,
                                                                                                out2,
                                                                                                &mut
                                                                                                pcount1,
                                                                                                &mut
                                                                                                psize1
                                                                                            );
                                                                                        if ! res20
                                                                                        {
                                                                                            (&mut
                                                                                            pres)[0usize] =
                                                                                                false
                                                                                        };
                                                                                        let
                                                                                        c40:
                                                                                        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
                                                                                        =
                                                                                            (&pc)[0usize];
                                                                                        let
                                                                                        em10: bool
                                                                                        =
                                                                                            crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                                                                c40.cddl_array_iterator_contents
                                                                                            );
                                                                                        let
                                                                                        res21: bool
                                                                                        =
                                                                                            (&pres)[0usize];
                                                                                        cond =
                                                                                            res21
                                                                                            &&
                                                                                            ! em10
                                                                                    };
                                                                                    let ret: bool =
                                                                                        (&pres)[0usize];
                                                                                    if ret
                                                                                    { ret }
                                                                                    else
                                                                                    { ret }
                                                                                }
                                                                            },
                                                                          _ =>
                                                                            panic!(
                                                                                "Incomplete pattern matching"
                                                                            )
                                                                      };
                                                                  let res21: usize =
                                                                      if res2
                                                                      {
                                                                          let size: usize =
                                                                              (&psize1)[0usize];
                                                                          let count1: u64 =
                                                                              (&pcount1)[0usize];
                                                                          crate::cbordetver::cbor_det_serialize_array(
                                                                              count1,
                                                                              out2,
                                                                              size
                                                                          )
                                                                      }
                                                                      else
                                                                      { 0usize };
                                                                  if res21 > 0usize
                                                                  {
                                                                      let size2: usize =
                                                                          size1.wrapping_add(res21);
                                                                      let
                                                                      _letpattern3:
                                                                      (&mut [u8], &mut [u8])
                                                                      =
                                                                          out.split_at_mut(size2);
                                                                      let out012: &mut [u8] =
                                                                          _letpattern3.0;
                                                                      let _out_rest: &[u8] =
                                                                          _letpattern3.1;
                                                                      let res3: bool =
                                                                          crate::cbordetver::cbor_det_serialize_map_insert(
                                                                              out012,
                                                                              size0,
                                                                              size1
                                                                          );
                                                                      if res3
                                                                      {
                                                                          (&mut psize)[0usize] =
                                                                              size2;
                                                                          (&mut pcount)[0usize] =
                                                                              count.wrapping_add(
                                                                                  1u64
                                                                              );
                                                                          true
                                                                      }
                                                                      else
                                                                      { false }
                                                                  }
                                                                  else
                                                                  { false }
                                                              }
                                                              else
                                                              { false }
                                                          }
                                                          else
                                                          { false }
                                                      },
                                                    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label::None
                                                    => true,
                                                    _ => panic!("Incomplete pattern matching")
                                                }
                                            }
                                            else
                                            { false }
                                        };
                                    if res1
                                    {
                                        match c23
                                        {
                                            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Some
                                            { v: c14 }
                                            =>
                                              {
                                                  let count: u64 = (&pcount)[0usize];
                                                  if count < 18446744073709551615u64
                                                  {
                                                      let size0: usize = (&psize)[0usize];
                                                      let _letpattern1: (&mut [u8], &mut [u8]) =
                                                          out.split_at_mut(size0);
                                                      let _out0: &[u8] = _letpattern1.0;
                                                      let out1: &mut [u8] = _letpattern1.1;
                                                      let
                                                      mty: crate::cbordetver::cbor_det_int_kind
                                                      =
                                                          crate::cbordetver::cbor_det_int_kind::UInt64;
                                                      let c3: crate::cbordetveraux::cbor_raw =
                                                          crate::cbordetver::cbor_det_mk_int64(
                                                              mty,
                                                              3u64
                                                          );
                                                      let res: crate::cbordetver::option__size_t =
                                                          crate::cbordetver::cbor_det_serialize(
                                                              c3,
                                                              out1
                                                          );
                                                      let res11: usize =
                                                          match res
                                                          {
                                                              crate::cbordetver::option__size_t::None
                                                              => 0usize,
                                                              crate::cbordetver::option__size_t::Some
                                                              { v: r }
                                                              => r,
                                                              _ =>
                                                                panic!(
                                                                    "Incomplete pattern matching"
                                                                )
                                                          };
                                                      if res11 > 0usize
                                                      {
                                                          let size1: usize =
                                                              size0.wrapping_add(res11);
                                                          let _letpattern2: (&mut [u8], &mut [u8]) =
                                                              out.split_at_mut(size1);
                                                          let _out01: &[u8] = _letpattern2.0;
                                                          let out2: &mut [u8] = _letpattern2.1;
                                                          let res2: usize =
                                                              match c14
                                                              {
                                                                  either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Inl
                                                                  { v: c15 }
                                                                  => serialize_tstr(c15, out2),
                                                                  either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Inr
                                                                  { v: c24 }
                                                                  => serialize_int(c24, out2),
                                                                  _ =>
                                                                    panic!(
                                                                        "Incomplete pattern matching"
                                                                    )
                                                              };
                                                          if res2 > 0usize
                                                          {
                                                              let size2: usize =
                                                                  size1.wrapping_add(res2);
                                                              let
                                                              _letpattern3: (&mut [u8], &mut [u8])
                                                              =
                                                                  out.split_at_mut(size2);
                                                              let out012: &mut [u8] =
                                                                  _letpattern3.0;
                                                              let _out_rest: &[u8] = _letpattern3.1;
                                                              let res3: bool =
                                                                  crate::cbordetver::cbor_det_serialize_map_insert(
                                                                      out012,
                                                                      size0,
                                                                      size1
                                                                  );
                                                              if res3
                                                              {
                                                                  (&mut psize)[0usize] = size2;
                                                                  (&mut pcount)[0usize] =
                                                                      count.wrapping_add(1u64);
                                                                  true
                                                              }
                                                              else
                                                              { false }
                                                          }
                                                          else
                                                          { false }
                                                      }
                                                      else
                                                      { false }
                                                  }
                                                  else
                                                  { false }
                                              },
                                            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::None
                                            => true,
                                            _ => panic!("Incomplete pattern matching")
                                        }
                                    }
                                    else
                                    { false }
                                };
                            if res1
                            {
                                match c22
                                {
                                    option__Pulse_Lib_Slice_slice·uint8_t::Some { v: c13 } =>
                                      {
                                          let count: u64 = (&pcount)[0usize];
                                          if count < 18446744073709551615u64
                                          {
                                              let size0: usize = (&psize)[0usize];
                                              let _letpattern1: (&mut [u8], &mut [u8]) =
                                                  out.split_at_mut(size0);
                                              let _out0: &[u8] = _letpattern1.0;
                                              let out1: &mut [u8] = _letpattern1.1;
                                              let mty: crate::cbordetver::cbor_det_int_kind =
                                                  crate::cbordetver::cbor_det_int_kind::UInt64;
                                              let c3: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_mk_int64(mty, 4u64);
                                              let res: crate::cbordetver::option__size_t =
                                                  crate::cbordetver::cbor_det_serialize(c3, out1);
                                              let res11: usize =
                                                  match res
                                                  {
                                                      crate::cbordetver::option__size_t::None =>
                                                        0usize,
                                                      crate::cbordetver::option__size_t::Some
                                                      { v: r }
                                                      => r,
                                                      _ => panic!("Incomplete pattern matching")
                                                  };
                                              if res11 > 0usize
                                              {
                                                  let size1: usize = size0.wrapping_add(res11);
                                                  let _letpattern2: (&mut [u8], &mut [u8]) =
                                                      out.split_at_mut(size1);
                                                  let _out01: &[u8] = _letpattern2.0;
                                                  let out2: &mut [u8] = _letpattern2.1;
                                                  let res2: usize = serialize_bstr(c13, out2);
                                                  if res2 > 0usize
                                                  {
                                                      let size2: usize = size1.wrapping_add(res2);
                                                      let _letpattern3: (&mut [u8], &mut [u8]) =
                                                          out.split_at_mut(size2);
                                                      let out012: &mut [u8] = _letpattern3.0;
                                                      let _out_rest: &[u8] = _letpattern3.1;
                                                      let res3: bool =
                                                          crate::cbordetver::cbor_det_serialize_map_insert(
                                                              out012,
                                                              size0,
                                                              size1
                                                          );
                                                      if res3
                                                      {
                                                          (&mut psize)[0usize] = size2;
                                                          (&mut pcount)[0usize] =
                                                              count.wrapping_add(1u64);
                                                          true
                                                      }
                                                      else
                                                      { false }
                                                  }
                                                  else
                                                  { false }
                                              }
                                              else
                                              { false }
                                          }
                                          else
                                          { false }
                                      },
                                    option__Pulse_Lib_Slice_slice·uint8_t::None => true,
                                    _ => panic!("Incomplete pattern matching")
                                }
                            }
                            else
                            { false }
                        };
                    if res1
                    {
                        match c21
                        {
                            either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_FStar_Pervasives_either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···::Inl
                            { v: c12 }
                            =>
                              {
                                  let c13: &[u8] = c12.0;
                                  let
                                  c22:
                                  crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags
                                  =
                                      c12.1;
                                  let count: u64 = (&pcount)[0usize];
                                  let res11: bool =
                                      if count < 18446744073709551615u64
                                      {
                                          let size0: usize = (&psize)[0usize];
                                          let _letpattern1: (&mut [u8], &mut [u8]) =
                                              out.split_at_mut(size0);
                                          let _out0: &[u8] = _letpattern1.0;
                                          let out1: &mut [u8] = _letpattern1.1;
                                          let mty: crate::cbordetver::cbor_det_int_kind =
                                              crate::cbordetver::cbor_det_int_kind::UInt64;
                                          let c3: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_mk_int64(mty, 5u64);
                                          let res: crate::cbordetver::option__size_t =
                                              crate::cbordetver::cbor_det_serialize(c3, out1);
                                          let res11: usize =
                                              match res
                                              {
                                                  crate::cbordetver::option__size_t::None => 0usize,
                                                  crate::cbordetver::option__size_t::Some
                                                  { v: r }
                                                  => r,
                                                  _ => panic!("Incomplete pattern matching")
                                              };
                                          if res11 > 0usize
                                          {
                                              let size1: usize = size0.wrapping_add(res11);
                                              let _letpattern2: (&mut [u8], &mut [u8]) =
                                                  out.split_at_mut(size1);
                                              let _out01: &[u8] = _letpattern2.0;
                                              let out2: &mut [u8] = _letpattern2.1;
                                              let res2: usize = serialize_bstr(c13, out2);
                                              if res2 > 0usize
                                              {
                                                  let size2: usize = size1.wrapping_add(res2);
                                                  let _letpattern3: (&mut [u8], &mut [u8]) =
                                                      out.split_at_mut(size2);
                                                  let out012: &mut [u8] = _letpattern3.0;
                                                  let _out_rest: &[u8] = _letpattern3.1;
                                                  let res3: bool =
                                                      crate::cbordetver::cbor_det_serialize_map_insert(
                                                          out012,
                                                          size0,
                                                          size1
                                                      );
                                                  if res3
                                                  {
                                                      (&mut psize)[0usize] = size2;
                                                      (&mut pcount)[0usize] =
                                                          count.wrapping_add(1u64);
                                                      true
                                                  }
                                                  else
                                                  { false }
                                              }
                                              else
                                              { false }
                                          }
                                          else
                                          { false }
                                      }
                                      else
                                      { false };
                                  if res11
                                  {
                                      match c22
                                      {
                                          crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags::Some
                                          =>
                                            {
                                                let count1: u64 = (&pcount)[0usize];
                                                if count1 < 18446744073709551615u64
                                                {
                                                    let size0: usize = (&psize)[0usize];
                                                    let _letpattern1: (&mut [u8], &mut [u8]) =
                                                        out.split_at_mut(size0);
                                                    let _out0: &[u8] = _letpattern1.0;
                                                    let out1: &mut [u8] = _letpattern1.1;
                                                    let mty: crate::cbordetver::cbor_det_int_kind =
                                                        crate::cbordetver::cbor_det_int_kind::UInt64;
                                                    let c3: crate::cbordetveraux::cbor_raw =
                                                        crate::cbordetver::cbor_det_mk_int64(
                                                            mty,
                                                            6u64
                                                        );
                                                    let res: crate::cbordetver::option__size_t =
                                                        crate::cbordetver::cbor_det_serialize(
                                                            c3,
                                                            out1
                                                        );
                                                    let res12: usize =
                                                        match res
                                                        {
                                                            crate::cbordetver::option__size_t::None
                                                            => 0usize,
                                                            crate::cbordetver::option__size_t::Some
                                                            { v: r }
                                                            => r,
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        };
                                                    if res12 > 0usize
                                                    {
                                                        let size1: usize =
                                                            size0.wrapping_add(res12);
                                                        let _letpattern2: (&[u8], &[u8]) =
                                                            out.split_at(size1);
                                                        let _out01: &[u8] = _letpattern2.0;
                                                        let out2: &[u8] = _letpattern2.1;
                                                        let res2: usize =
                                                            serialize_everparsenomatch(out2);
                                                        if res2 > 0usize
                                                        {
                                                            let size2: usize =
                                                                size1.wrapping_add(res2);
                                                            let
                                                            _letpattern3: (&mut [u8], &mut [u8])
                                                            =
                                                                out.split_at_mut(size2);
                                                            let out012: &mut [u8] = _letpattern3.0;
                                                            let _out_rest: &[u8] = _letpattern3.1;
                                                            let res3: bool =
                                                                crate::cbordetver::cbor_det_serialize_map_insert(
                                                                    out012,
                                                                    size0,
                                                                    size1
                                                                );
                                                            if res3
                                                            {
                                                                (&mut psize)[0usize] = size2;
                                                                (&mut pcount)[0usize] =
                                                                    count1.wrapping_add(1u64);
                                                                true
                                                            }
                                                            else
                                                            { false }
                                                        }
                                                        else
                                                        { false }
                                                    }
                                                    else
                                                    { false }
                                                }
                                                else
                                                { false }
                                            },
                                          crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags::None
                                          => true,
                                          _ =>
                                            panic!(
                                                "Precondition of the function most likely violated"
                                            )
                                      }
                                  }
                                  else
                                  { false }
                              },
                            either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_FStar_Pervasives_either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···::Inr
                            { v: c22 }
                            =>
                              match c22
                              {
                                  either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···::Inl
                                  { v: c12 }
                                  =>
                                    {
                                        let c13: &[u8] = c12.0;
                                        let
                                        c23:
                                        crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags
                                        =
                                            c12.1;
                                        let count: u64 = (&pcount)[0usize];
                                        let res11: bool =
                                            if count < 18446744073709551615u64
                                            {
                                                let size0: usize = (&psize)[0usize];
                                                let _letpattern1: (&mut [u8], &mut [u8]) =
                                                    out.split_at_mut(size0);
                                                let _out0: &[u8] = _letpattern1.0;
                                                let out1: &mut [u8] = _letpattern1.1;
                                                let mty: crate::cbordetver::cbor_det_int_kind =
                                                    crate::cbordetver::cbor_det_int_kind::UInt64;
                                                let c3: crate::cbordetveraux::cbor_raw =
                                                    crate::cbordetver::cbor_det_mk_int64(mty, 6u64);
                                                let res: crate::cbordetver::option__size_t =
                                                    crate::cbordetver::cbor_det_serialize(c3, out1);
                                                let res11: usize =
                                                    match res
                                                    {
                                                        crate::cbordetver::option__size_t::None =>
                                                          0usize,
                                                        crate::cbordetver::option__size_t::Some
                                                        { v: r }
                                                        => r,
                                                        _ => panic!("Incomplete pattern matching")
                                                    };
                                                if res11 > 0usize
                                                {
                                                    let size1: usize = size0.wrapping_add(res11);
                                                    let _letpattern2: (&mut [u8], &mut [u8]) =
                                                        out.split_at_mut(size1);
                                                    let _out01: &[u8] = _letpattern2.0;
                                                    let out2: &mut [u8] = _letpattern2.1;
                                                    let res2: usize = serialize_bstr(c13, out2);
                                                    if res2 > 0usize
                                                    {
                                                        let size2: usize = size1.wrapping_add(res2);
                                                        let _letpattern3: (&mut [u8], &mut [u8]) =
                                                            out.split_at_mut(size2);
                                                        let out012: &mut [u8] = _letpattern3.0;
                                                        let _out_rest: &[u8] = _letpattern3.1;
                                                        let res3: bool =
                                                            crate::cbordetver::cbor_det_serialize_map_insert(
                                                                out012,
                                                                size0,
                                                                size1
                                                            );
                                                        if res3
                                                        {
                                                            (&mut psize)[0usize] = size2;
                                                            (&mut pcount)[0usize] =
                                                                count.wrapping_add(1u64);
                                                            true
                                                        }
                                                        else
                                                        { false }
                                                    }
                                                    else
                                                    { false }
                                                }
                                                else
                                                { false }
                                            }
                                            else
                                            { false };
                                        if res11
                                        {
                                            match c23
                                            {
                                                crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags::Some
                                                =>
                                                  {
                                                      let count1: u64 = (&pcount)[0usize];
                                                      if count1 < 18446744073709551615u64
                                                      {
                                                          let size0: usize = (&psize)[0usize];
                                                          let _letpattern1: (&mut [u8], &mut [u8]) =
                                                              out.split_at_mut(size0);
                                                          let _out0: &[u8] = _letpattern1.0;
                                                          let out1: &mut [u8] = _letpattern1.1;
                                                          let
                                                          mty: crate::cbordetver::cbor_det_int_kind
                                                          =
                                                              crate::cbordetver::cbor_det_int_kind::UInt64;
                                                          let c3: crate::cbordetveraux::cbor_raw =
                                                              crate::cbordetver::cbor_det_mk_int64(
                                                                  mty,
                                                                  5u64
                                                              );
                                                          let
                                                          res: crate::cbordetver::option__size_t
                                                          =
                                                              crate::cbordetver::cbor_det_serialize(
                                                                  c3,
                                                                  out1
                                                              );
                                                          let res12: usize =
                                                              match res
                                                              {
                                                                  crate::cbordetver::option__size_t::None
                                                                  => 0usize,
                                                                  crate::cbordetver::option__size_t::Some
                                                                  { v: r }
                                                                  => r,
                                                                  _ =>
                                                                    panic!(
                                                                        "Incomplete pattern matching"
                                                                    )
                                                              };
                                                          if res12 > 0usize
                                                          {
                                                              let size1: usize =
                                                                  size0.wrapping_add(res12);
                                                              let _letpattern2: (&[u8], &[u8]) =
                                                                  out.split_at(size1);
                                                              let _out01: &[u8] = _letpattern2.0;
                                                              let out2: &[u8] = _letpattern2.1;
                                                              let res2: usize =
                                                                  serialize_everparsenomatch(out2);
                                                              if res2 > 0usize
                                                              {
                                                                  let size2: usize =
                                                                      size1.wrapping_add(res2);
                                                                  let
                                                                  _letpattern3:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size2);
                                                                  let out012: &mut [u8] =
                                                                      _letpattern3.0;
                                                                  let _out_rest: &[u8] =
                                                                      _letpattern3.1;
                                                                  let res3: bool =
                                                                      crate::cbordetver::cbor_det_serialize_map_insert(
                                                                          out012,
                                                                          size0,
                                                                          size1
                                                                      );
                                                                  if res3
                                                                  {
                                                                      (&mut psize)[0usize] = size2;
                                                                      (&mut pcount)[0usize] =
                                                                          count1.wrapping_add(1u64);
                                                                      true
                                                                  }
                                                                  else
                                                                  { false }
                                                              }
                                                              else
                                                              { false }
                                                          }
                                                          else
                                                          { false }
                                                      }
                                                      else
                                                      { false }
                                                  },
                                                crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags::None
                                                => true,
                                                _ =>
                                                  panic!(
                                                      "Precondition of the function most likely violated"
                                                  )
                                            }
                                        }
                                        else
                                        { false }
                                    },
                                  either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···::Inr
                                  { v: c23 }
                                  =>
                                    {
                                        let
                                        c12:
                                        crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags
                                        =
                                            c23.0;
                                        let
                                        c24:
                                        crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags
                                        =
                                            c23.1;
                                        let res11: bool =
                                            match c12
                                            {
                                                crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags::Some
                                                =>
                                                  {
                                                      let count: u64 = (&pcount)[0usize];
                                                      if count < 18446744073709551615u64
                                                      {
                                                          let size0: usize = (&psize)[0usize];
                                                          let _letpattern1: (&mut [u8], &mut [u8]) =
                                                              out.split_at_mut(size0);
                                                          let _out0: &[u8] = _letpattern1.0;
                                                          let out1: &mut [u8] = _letpattern1.1;
                                                          let
                                                          mty: crate::cbordetver::cbor_det_int_kind
                                                          =
                                                              crate::cbordetver::cbor_det_int_kind::UInt64;
                                                          let c3: crate::cbordetveraux::cbor_raw =
                                                              crate::cbordetver::cbor_det_mk_int64(
                                                                  mty,
                                                                  6u64
                                                              );
                                                          let
                                                          res: crate::cbordetver::option__size_t
                                                          =
                                                              crate::cbordetver::cbor_det_serialize(
                                                                  c3,
                                                                  out1
                                                              );
                                                          let res11: usize =
                                                              match res
                                                              {
                                                                  crate::cbordetver::option__size_t::None
                                                                  => 0usize,
                                                                  crate::cbordetver::option__size_t::Some
                                                                  { v: r }
                                                                  => r,
                                                                  _ =>
                                                                    panic!(
                                                                        "Incomplete pattern matching"
                                                                    )
                                                              };
                                                          if res11 > 0usize
                                                          {
                                                              let size1: usize =
                                                                  size0.wrapping_add(res11);
                                                              let _letpattern2: (&[u8], &[u8]) =
                                                                  out.split_at(size1);
                                                              let _out01: &[u8] = _letpattern2.0;
                                                              let out2: &[u8] = _letpattern2.1;
                                                              let res2: usize =
                                                                  serialize_everparsenomatch(out2);
                                                              if res2 > 0usize
                                                              {
                                                                  let size2: usize =
                                                                      size1.wrapping_add(res2);
                                                                  let
                                                                  _letpattern3:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size2);
                                                                  let out012: &mut [u8] =
                                                                      _letpattern3.0;
                                                                  let _out_rest: &[u8] =
                                                                      _letpattern3.1;
                                                                  let res3: bool =
                                                                      crate::cbordetver::cbor_det_serialize_map_insert(
                                                                          out012,
                                                                          size0,
                                                                          size1
                                                                      );
                                                                  if res3
                                                                  {
                                                                      (&mut psize)[0usize] = size2;
                                                                      (&mut pcount)[0usize] =
                                                                          count.wrapping_add(1u64);
                                                                      true
                                                                  }
                                                                  else
                                                                  { false }
                                                              }
                                                              else
                                                              { false }
                                                          }
                                                          else
                                                          { false }
                                                      }
                                                      else
                                                      { false }
                                                  },
                                                crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags::None
                                                => true,
                                                _ =>
                                                  panic!(
                                                      "Precondition of the function most likely violated"
                                                  )
                                            };
                                        if res11
                                        {
                                            match c24
                                            {
                                                crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags::Some
                                                =>
                                                  {
                                                      let count: u64 = (&pcount)[0usize];
                                                      if count < 18446744073709551615u64
                                                      {
                                                          let size0: usize = (&psize)[0usize];
                                                          let _letpattern1: (&mut [u8], &mut [u8]) =
                                                              out.split_at_mut(size0);
                                                          let _out0: &[u8] = _letpattern1.0;
                                                          let out1: &mut [u8] = _letpattern1.1;
                                                          let
                                                          mty: crate::cbordetver::cbor_det_int_kind
                                                          =
                                                              crate::cbordetver::cbor_det_int_kind::UInt64;
                                                          let c3: crate::cbordetveraux::cbor_raw =
                                                              crate::cbordetver::cbor_det_mk_int64(
                                                                  mty,
                                                                  5u64
                                                              );
                                                          let
                                                          res: crate::cbordetver::option__size_t
                                                          =
                                                              crate::cbordetver::cbor_det_serialize(
                                                                  c3,
                                                                  out1
                                                              );
                                                          let res12: usize =
                                                              match res
                                                              {
                                                                  crate::cbordetver::option__size_t::None
                                                                  => 0usize,
                                                                  crate::cbordetver::option__size_t::Some
                                                                  { v: r }
                                                                  => r,
                                                                  _ =>
                                                                    panic!(
                                                                        "Incomplete pattern matching"
                                                                    )
                                                              };
                                                          if res12 > 0usize
                                                          {
                                                              let size1: usize =
                                                                  size0.wrapping_add(res12);
                                                              let _letpattern2: (&[u8], &[u8]) =
                                                                  out.split_at(size1);
                                                              let _out01: &[u8] = _letpattern2.0;
                                                              let out2: &[u8] = _letpattern2.1;
                                                              let res2: usize =
                                                                  serialize_everparsenomatch(out2);
                                                              if res2 > 0usize
                                                              {
                                                                  let size2: usize =
                                                                      size1.wrapping_add(res2);
                                                                  let
                                                                  _letpattern3:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size2);
                                                                  let out012: &mut [u8] =
                                                                      _letpattern3.0;
                                                                  let _out_rest: &[u8] =
                                                                      _letpattern3.1;
                                                                  let res3: bool =
                                                                      crate::cbordetver::cbor_det_serialize_map_insert(
                                                                          out012,
                                                                          size0,
                                                                          size1
                                                                      );
                                                                  if res3
                                                                  {
                                                                      (&mut psize)[0usize] = size2;
                                                                      (&mut pcount)[0usize] =
                                                                          count.wrapping_add(1u64);
                                                                      true
                                                                  }
                                                                  else
                                                                  { false }
                                                              }
                                                              else
                                                              { false }
                                                          }
                                                          else
                                                          { false }
                                                      }
                                                      else
                                                      { false }
                                                  },
                                                crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags::None
                                                => true,
                                                _ =>
                                                  panic!(
                                                      "Precondition of the function most likely violated"
                                                  )
                                            }
                                        }
                                        else
                                        { false }
                                    },
                                  _ => panic!("Incomplete pattern matching")
                              },
                            _ => panic!("Incomplete pattern matching")
                        }
                    }
                    else
                    { false }
                };
            if res1
            {
                match c2
                {
                    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw::Inl
                    { v: c11 }
                    =>
                      {
                          let discarded: [&[(evercddl_label, crate::cbordetveraux::cbor_raw)]; 1] =
                              [c11; 1usize];
                          crate::lowstar::ignore::ignore::<[&[(evercddl_label,
                          crate::cbordetveraux::cbor_raw)];
                          1]>(discarded);
                          let mut pres: [bool; 1] = [true; 1usize];
                          let mut pc: [&[(evercddl_label, crate::cbordetveraux::cbor_raw)]; 1] =
                              [c11; 1usize];
                          let em0: bool = c11.len() == 0usize;
                          let mut pem: [bool; 1] = [em0; 1usize];
                          let __anf1: bool = (&pres)[0usize];
                          let __anf0: bool = (&pem)[0usize];
                          let mut cond: bool = __anf1 && ! __anf0;
                          while
                          cond
                          {
                              let count: u64 = (&pcount)[0usize];
                              if count == 18446744073709551615u64
                              { (&mut pres)[0usize] = false }
                              else
                              {
                                  let count·: u64 = count.wrapping_add(1u64);
                                  let i: &[(evercddl_label, crate::cbordetveraux::cbor_raw)] =
                                      (&pc)[0usize];
                                  let res: (evercddl_label, crate::cbordetveraux::cbor_raw) =
                                      i[0usize];
                                  let
                                  _letpattern1:
                                  (&[(evercddl_label, crate::cbordetveraux::cbor_raw)],
                                  &[(evercddl_label, crate::cbordetveraux::cbor_raw)])
                                  =
                                      i.split_at(1usize);
                                  let
                                  _letpattern2: (evercddl_label, crate::cbordetveraux::cbor_raw)
                                  =
                                      {
                                          let
                                          _il: &[(evercddl_label, crate::cbordetveraux::cbor_raw)]
                                          =
                                              _letpattern1.0;
                                          let
                                          ir: &[(evercddl_label, crate::cbordetveraux::cbor_raw)]
                                          =
                                              _letpattern1.1;
                                          (&mut pc)[0usize] = ir;
                                          res
                                      };
                                  let ek: evercddl_label = _letpattern2.0;
                                  let ev: crate::cbordetveraux::cbor_raw = _letpattern2.1;
                                  let size0: usize = (&psize)[0usize];
                                  let _letpattern3: (&mut [u8], &mut [u8]) =
                                      out.split_at_mut(size0);
                                  let _tmp: &[u8] = _letpattern3.0;
                                  let out1: &mut [u8] = _letpattern3.1;
                                  let size1: usize = serialize_evercddl_label(ek, out1);
                                  if size1 == 0usize
                                  { (&mut pres)[0usize] = false }
                                  else
                                  {
                                      let _letpattern4: (&mut [u8], &mut [u8]) =
                                          out1.split_at_mut(size1);
                                      let out1·: &[u8] = _letpattern4.0;
                                      let out2: &mut [u8] = _letpattern4.1;
                                      let size2: usize = serialize_values(ev, out2);
                                      if size2 == 0usize
                                      { (&mut pres)[0usize] = false }
                                      else
                                      {
                                          let
                                          res2:
                                          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                          =
                                              crate::cbordetver::cbor_det_parse(out1·);
                                          let
                                          ock:
                                          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                          =
                                              match res2
                                              {
                                                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
                                                  =>
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None,
                                                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                  { v: pair }
                                                  =>
                                                    {
                                                        let c3: crate::cbordetveraux::cbor_raw =
                                                            pair.0;
                                                        let rem: &[u8] = pair.1;
                                                        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                        { v: (c3,rem) }
                                                    },
                                                  _ => panic!("Incomplete pattern matching")
                                              };
                                          match ock
                                          {
                                              crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                              { v: ck_ }
                                              =>
                                                {
                                                    let ck: crate::cbordetveraux::cbor_raw = ck_.0;
                                                    let _remk: &[u8] = ck_.1;
                                                    let _letpattern5: (&[u8], &[u8]) =
                                                        out2.split_at(size2);
                                                    let out2·: &[u8] = _letpattern5.0;
                                                    let _out2_tail: &[u8] = _letpattern5.1;
                                                    let
                                                    res3:
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                                    =
                                                        crate::cbordetver::cbor_det_parse(out2·);
                                                    let
                                                    ocv:
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                                    =
                                                        match res3
                                                        {
                                                            crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
                                                            =>
                                                              crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None,
                                                            crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                            { v: pair }
                                                            =>
                                                              {
                                                                  let
                                                                  c3: crate::cbordetveraux::cbor_raw
                                                                  =
                                                                      pair.0;
                                                                  let rem: &[u8] = pair.1;
                                                                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                                  { v: (c3,rem) }
                                                              },
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        };
                                                    match ocv
                                                    {
                                                        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                        { v: cv_ }
                                                        =>
                                                          {
                                                              let
                                                              cv: crate::cbordetveraux::cbor_raw
                                                              =
                                                                  cv_.0;
                                                              let _remv: &[u8] = cv_.1;
                                                              let
                                                              ce:
                                                              crate::cbordetveraux::cbor_map_entry
                                                              =
                                                                  crate::cbordetver::cbor_det_mk_map_entry(
                                                                      ck,
                                                                      cv
                                                                  );
                                                              let ex: bool =
                                                                  aux_env34_map_constraint_2(ce);
                                                              if ex
                                                              { (&mut pres)[0usize] = false }
                                                              else
                                                              {
                                                                  let size1·: usize =
                                                                      size0.wrapping_add(size1);
                                                                  let size2·: usize =
                                                                      size1·.wrapping_add(size2);
                                                                  let
                                                                  _letpattern6:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size2·);
                                                                  let out_: &mut [u8] =
                                                                      _letpattern6.0;
                                                                  let _tmp1: &[u8] = _letpattern6.1;
                                                                  let no_dup: bool =
                                                                      crate::cbordetver::cbor_det_serialize_map_insert(
                                                                          out_,
                                                                          size0,
                                                                          size1·
                                                                      );
                                                                  if no_dup
                                                                  {
                                                                      let
                                                                      __anf00:
                                                                      &[(evercddl_label,
                                                                      crate::cbordetveraux::cbor_raw)]
                                                                      =
                                                                          (&pc)[0usize];
                                                                      let __anf10: bool =
                                                                          __anf00.len() == 0usize;
                                                                      (&mut pem)[0usize] = __anf10;
                                                                      (&mut psize)[0usize] = size2·;
                                                                      (&mut pcount)[0usize] =
                                                                          count·
                                                                  }
                                                                  else
                                                                  { (&mut pres)[0usize] = false }
                                                              }
                                                          },
                                                        _ => panic!("Incomplete pattern matching")
                                                    }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          }
                                      }
                                  }
                              };
                              let __anf10: bool = (&pres)[0usize];
                              let __anf00: bool = (&pem)[0usize];
                              cond = __anf10 && ! __anf00
                          };
                          (&pres)[0usize]
                      },
                    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw::Inr
                    { v: c21 }
                    =>
                      {
                          let mut pres: [bool; 1] = [true; 1usize];
                          let
                          mut
                          pc:
                          [map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw;
                          1]
                          =
                              [c21; 1usize];
                          let
                          mut
                          pj:
                          [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry;
                          1]
                          =
                              [c21.cddl_map_iterator_contents; 1usize];
                          let mut pres1: [bool; 1] = [true; 1usize];
                          let
                          j:
                          crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                          =
                              (&pj)[0usize];
                          let test: bool = crate::cbordetver::cbor_det_map_iterator_is_empty(j);
                          let res: bool = (&pres1)[0usize];
                          let mut cond: bool = res && ! test;
                          while
                          cond
                          {
                              let elt: crate::cbordetveraux::cbor_map_entry =
                                  crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
                              let elt_key: crate::cbordetveraux::cbor_raw =
                                  crate::cbordetver::cbor_det_map_entry_key(elt);
                              let test_key: bool = (c21.cddl_map_iterator_impl_validate1)(elt_key);
                              if ! ! test_key
                              {
                                  let test_ex: bool = (c21.cddl_map_iterator_impl_validate_ex)(elt);
                                  if ! test_ex
                                  {
                                      let elt_value: crate::cbordetveraux::cbor_raw =
                                          crate::cbordetver::cbor_det_map_entry_value(elt);
                                      let test_value: bool =
                                          (c21.cddl_map_iterator_impl_validate2)(elt_value);
                                      (&mut pres1)[0usize] = ! test_value
                                  }
                              };
                              let
                              j0:
                              crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                              =
                                  (&pj)[0usize];
                              let test0: bool =
                                  crate::cbordetver::cbor_det_map_iterator_is_empty(j0);
                              let res0: bool = (&pres1)[0usize];
                              cond = res0 && ! test0
                          };
                          let em0: bool = (&pres1)[0usize];
                          let mut pem: [bool; 1] = [em0; 1usize];
                          let __anf1: bool = (&pres)[0usize];
                          let __anf0: bool = (&pem)[0usize];
                          let mut cond0: bool = __anf1 && ! __anf0;
                          while
                          cond0
                          {
                              let count: u64 = (&pcount)[0usize];
                              if count == 18446744073709551615u64
                              { (&mut pres)[0usize] = false }
                              else
                              {
                                  let count·: u64 = count.wrapping_add(1u64);
                                  let
                                  i:
                                  map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
                                  =
                                      (&pc)[0usize];
                                  let
                                  mut
                                  pj1:
                                  [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry;
                                  1]
                                  =
                                      [i.cddl_map_iterator_contents; 1usize];
                                  let hd0: crate::cbordetveraux::cbor_map_entry =
                                      crate::cbordetver::cbor_det_map_iterator_next(&mut pj1);
                                  let mut phd: [crate::cbordetveraux::cbor_map_entry; 1] =
                                      [hd0; 1usize];
                                  let hk0: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_key(hd0);
                                  let tk0: bool = (i.cddl_map_iterator_impl_validate1)(hk0);
                                  let hv0: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_value(hd0);
                                  let tv0: bool = (i.cddl_map_iterator_impl_validate2)(hv0);
                                  let te0: bool = (i.cddl_map_iterator_impl_validate_ex)(hd0);
                                  let mut pcont: [bool; 1] = [! tk0 || ! tv0 || te0; 1usize];
                                  while
                                  (&pcont)[0usize]
                                  {
                                      let hd: crate::cbordetveraux::cbor_map_entry =
                                          crate::cbordetver::cbor_det_map_iterator_next(&mut pj1);
                                      (&mut phd)[0usize] = hd;
                                      let hk: crate::cbordetveraux::cbor_raw =
                                          crate::cbordetver::cbor_det_map_entry_key(hd);
                                      let tk: bool = (i.cddl_map_iterator_impl_validate1)(hk);
                                      let hv: crate::cbordetveraux::cbor_raw =
                                          crate::cbordetver::cbor_det_map_entry_value(hd);
                                      let tv: bool = (i.cddl_map_iterator_impl_validate2)(hv);
                                      let te: bool = (i.cddl_map_iterator_impl_validate_ex)(hd);
                                      (&mut pcont)[0usize] = ! tk || ! tv || te
                                  };
                                  let hd: crate::cbordetveraux::cbor_map_entry = (&phd)[0usize];
                                  let hd_key: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_key(hd);
                                  let hd_key_res: evercddl_label =
                                      (i.cddl_map_iterator_impl_parse1)(hd_key);
                                  let hd_value: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_value(hd);
                                  let hd_value_res: crate::cbordetveraux::cbor_raw =
                                      (i.cddl_map_iterator_impl_parse2)(hd_value);
                                  let
                                  j0:
                                  crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                  =
                                      (&pj1)[0usize];
                                  let
                                  i·:
                                  map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
                                  =
                                      map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
                                      {
                                          cddl_map_iterator_contents: j0,
                                          cddl_map_iterator_impl_validate1:
                                          i.cddl_map_iterator_impl_validate1,
                                          cddl_map_iterator_impl_parse1:
                                          i.cddl_map_iterator_impl_parse1,
                                          cddl_map_iterator_impl_validate_ex:
                                          i.cddl_map_iterator_impl_validate_ex,
                                          cddl_map_iterator_impl_validate2:
                                          i.cddl_map_iterator_impl_validate2,
                                          cddl_map_iterator_impl_parse2:
                                          i.cddl_map_iterator_impl_parse2
                                      };
                                  (&mut pc)[0usize] = i·;
                                  let
                                  _letpattern1: (evercddl_label, crate::cbordetveraux::cbor_raw)
                                  =
                                      (hd_key_res,hd_value_res);
                                  let ek: evercddl_label = _letpattern1.0;
                                  let ev: crate::cbordetveraux::cbor_raw = _letpattern1.1;
                                  let size0: usize = (&psize)[0usize];
                                  let _letpattern2: (&mut [u8], &mut [u8]) =
                                      out.split_at_mut(size0);
                                  let _tmp: &[u8] = _letpattern2.0;
                                  let out1: &mut [u8] = _letpattern2.1;
                                  let size1: usize = serialize_evercddl_label(ek, out1);
                                  if size1 == 0usize
                                  { (&mut pres)[0usize] = false }
                                  else
                                  {
                                      let _letpattern3: (&mut [u8], &mut [u8]) =
                                          out1.split_at_mut(size1);
                                      let out1·: &[u8] = _letpattern3.0;
                                      let out2: &mut [u8] = _letpattern3.1;
                                      let size2: usize = serialize_values(ev, out2);
                                      if size2 == 0usize
                                      { (&mut pres)[0usize] = false }
                                      else
                                      {
                                          let
                                          res0:
                                          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                          =
                                              crate::cbordetver::cbor_det_parse(out1·);
                                          let
                                          ock:
                                          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                          =
                                              match res0
                                              {
                                                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
                                                  =>
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None,
                                                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                  { v: pair }
                                                  =>
                                                    {
                                                        let c3: crate::cbordetveraux::cbor_raw =
                                                            pair.0;
                                                        let rem: &[u8] = pair.1;
                                                        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                        { v: (c3,rem) }
                                                    },
                                                  _ => panic!("Incomplete pattern matching")
                                              };
                                          match ock
                                          {
                                              crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                              { v: ck_ }
                                              =>
                                                {
                                                    let ck: crate::cbordetveraux::cbor_raw = ck_.0;
                                                    let _remk: &[u8] = ck_.1;
                                                    let _letpattern4: (&[u8], &[u8]) =
                                                        out2.split_at(size2);
                                                    let out2·: &[u8] = _letpattern4.0;
                                                    let _out2_tail: &[u8] = _letpattern4.1;
                                                    let
                                                    res2:
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                                    =
                                                        crate::cbordetver::cbor_det_parse(out2·);
                                                    let
                                                    ocv:
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                                    =
                                                        match res2
                                                        {
                                                            crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
                                                            =>
                                                              crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None,
                                                            crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                            { v: pair }
                                                            =>
                                                              {
                                                                  let
                                                                  c3: crate::cbordetveraux::cbor_raw
                                                                  =
                                                                      pair.0;
                                                                  let rem: &[u8] = pair.1;
                                                                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                                  { v: (c3,rem) }
                                                              },
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        };
                                                    match ocv
                                                    {
                                                        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                        { v: cv_ }
                                                        =>
                                                          {
                                                              let
                                                              cv: crate::cbordetveraux::cbor_raw
                                                              =
                                                                  cv_.0;
                                                              let _remv: &[u8] = cv_.1;
                                                              let
                                                              ce:
                                                              crate::cbordetveraux::cbor_map_entry
                                                              =
                                                                  crate::cbordetver::cbor_det_mk_map_entry(
                                                                      ck,
                                                                      cv
                                                                  );
                                                              let ex: bool =
                                                                  aux_env34_map_constraint_2(ce);
                                                              if ex
                                                              { (&mut pres)[0usize] = false }
                                                              else
                                                              {
                                                                  let size1·: usize =
                                                                      size0.wrapping_add(size1);
                                                                  let size2·: usize =
                                                                      size1·.wrapping_add(size2);
                                                                  let
                                                                  _letpattern5:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size2·);
                                                                  let out_: &mut [u8] =
                                                                      _letpattern5.0;
                                                                  let _tmp1: &[u8] = _letpattern5.1;
                                                                  let no_dup: bool =
                                                                      crate::cbordetver::cbor_det_serialize_map_insert(
                                                                          out_,
                                                                          size0,
                                                                          size1·
                                                                      );
                                                                  if no_dup
                                                                  {
                                                                      let
                                                                      __anf00:
                                                                      map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
                                                                      =
                                                                          (&pc)[0usize];
                                                                      let
                                                                      mut
                                                                      pj2:
                                                                      [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry;
                                                                      1]
                                                                      =
                                                                          [__anf00.cddl_map_iterator_contents;
                                                                              1usize];
                                                                      let mut pres2: [bool; 1] =
                                                                          [true; 1usize];
                                                                      let
                                                                      j1:
                                                                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                                                      =
                                                                          (&pj2)[0usize];
                                                                      let test0: bool =
                                                                          crate::cbordetver::cbor_det_map_iterator_is_empty(
                                                                              j1
                                                                          );
                                                                      let res3: bool =
                                                                          (&pres2)[0usize];
                                                                      let mut cond1: bool =
                                                                          res3 && ! test0;
                                                                      while
                                                                      cond1
                                                                      {
                                                                          let
                                                                          elt:
                                                                          crate::cbordetveraux::cbor_map_entry
                                                                          =
                                                                              crate::cbordetver::cbor_det_map_iterator_next(
                                                                                  &mut pj2
                                                                              );
                                                                          let
                                                                          elt_key:
                                                                          crate::cbordetveraux::cbor_raw
                                                                          =
                                                                              crate::cbordetver::cbor_det_map_entry_key(
                                                                                  elt
                                                                              );
                                                                          let test_key: bool =
                                                                              (__anf00.cddl_map_iterator_impl_validate1)(
                                                                                  elt_key
                                                                              );
                                                                          if ! ! test_key
                                                                          {
                                                                              let test_ex: bool =
                                                                                  (__anf00.cddl_map_iterator_impl_validate_ex)(
                                                                                      elt
                                                                                  );
                                                                              if ! test_ex
                                                                              {
                                                                                  let
                                                                                  elt_value:
                                                                                  crate::cbordetveraux::cbor_raw
                                                                                  =
                                                                                      crate::cbordetver::cbor_det_map_entry_value(
                                                                                          elt
                                                                                      );
                                                                                  let
                                                                                  test_value: bool
                                                                                  =
                                                                                      (__anf00.cddl_map_iterator_impl_validate2)(
                                                                                          elt_value
                                                                                      );
                                                                                  (&mut pres2)[0usize] =
                                                                                      ! test_value
                                                                              }
                                                                          };
                                                                          let
                                                                          j10:
                                                                          crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                                                          =
                                                                              (&pj2)[0usize];
                                                                          let test1: bool =
                                                                              crate::cbordetver::cbor_det_map_iterator_is_empty(
                                                                                  j10
                                                                              );
                                                                          let res30: bool =
                                                                              (&pres2)[0usize];
                                                                          cond1 = res30 && ! test1
                                                                      };
                                                                      let __anf10: bool =
                                                                          (&pres2)[0usize];
                                                                      (&mut pem)[0usize] = __anf10;
                                                                      (&mut psize)[0usize] = size2·;
                                                                      (&mut pcount)[0usize] =
                                                                          count·
                                                                  }
                                                                  else
                                                                  { (&mut pres)[0usize] = false }
                                                              }
                                                          },
                                                        _ => panic!("Incomplete pattern matching")
                                                    }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          }
                                      }
                                  }
                              };
                              let __anf10: bool = (&pres)[0usize];
                              let __anf00: bool = (&pem)[0usize];
                              cond0 = __anf10 && ! __anf00
                          };
                          (&pres)[0usize]
                      },
                    _ => panic!("Incomplete pattern matching")
                }
            }
            else
            { false }
        };
    if res
    {
        let size: usize = (&psize)[0usize];
        let count: u64 = (&pcount)[0usize];
        crate::cbordetver::cbor_det_serialize_map(count, out, size)
    }
    else
    { 0usize }
}

/**
Serializer for empty_or_serialized_map
*/
pub fn
serialize_empty_or_serialized_map(c: empty_or_serialized_map, out: &mut [u8]) ->
    usize
{
    match empty_or_serialized_map_left(c)
    {
        empty_or_serialized_map_ugly::Inl { v: c1 } =>
          {
              let sz: usize = serialize_header_map(c1, out);
              let fits: bool = crate::cbordetveraux::sizet_fits_u64(sz);
              if sz == 0usize || ! fits
              { 0usize }
              else
              {
                  crate::cbordetver::cbor_det_serialize_string(
                      crate::cbordetveraux::cbor_major_type_byte_string,
                      sz as u64,
                      out
                  )
              }
          },
        empty_or_serialized_map_ugly::Inr { v: c2 } =>
          {
              let len: usize = c2.len();
              let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(0u64, len);
              let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 0u64);
              if lo_ok && hi_ok
              {
                  if 2u8 == crate::cbordetveraux::cbor_major_type_byte_string
                  {
                      let len1: usize = c2.len();
                      let __anf0: bool =
                          crate::cbordetveraux::sizet_lte_u64(len1, 18446744073709551615u64);
                      if __anf0
                      {
                          let mty: crate::cbordetver::cbor_det_string_kind =
                              crate::cbordetver::cbor_det_string_kind::ByteString;
                          let res: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                              crate::cbordetver::cbor_det_mk_string(mty, c2);
                          let x: crate::cbordetveraux::cbor_raw =
                              match res
                              {
                                  crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                  { v: c1 }
                                  => c1,
                                  _ => panic!("Incomplete pattern matching")
                              };
                          let ser: crate::cbordetver::option__size_t =
                              crate::cbordetver::cbor_det_serialize(x, out);
                          match ser
                          {
                              crate::cbordetver::option__size_t::None => 0usize,
                              crate::cbordetver::option__size_t::Some { v: sz } => sz,
                              _ => panic!("Incomplete pattern matching")
                          }
                      }
                      else
                      { 0usize }
                  }
                  else
                  {
                      let len1: usize = c2.len();
                      let __anf0: bool =
                          crate::cbordetveraux::sizet_lte_u64(len1, 18446744073709551615u64);
                      if __anf0
                      {
                          let correct: bool = crate::cbordetver::cbor_impl_utf8_correct(c2);
                          if correct
                          {
                              let mty: crate::cbordetver::cbor_det_string_kind =
                                  if
                                  crate::cbordetveraux::cbor_major_type_text_string
                                  ==
                                  crate::cbordetveraux::cbor_major_type_byte_string
                                  { crate::cbordetver::cbor_det_string_kind::ByteString }
                                  else
                                  { crate::cbordetver::cbor_det_string_kind::TextString };
                              let res: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                                  crate::cbordetver::cbor_det_mk_string(mty, c2);
                              let x: crate::cbordetveraux::cbor_raw =
                                  match res
                                  {
                                      crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                      { v: c1 }
                                      => c1,
                                      _ => panic!("Incomplete pattern matching")
                                  };
                              let ser: crate::cbordetver::option__size_t =
                                  crate::cbordetver::cbor_det_serialize(x, out);
                              match ser
                              {
                                  crate::cbordetver::option__size_t::None => 0usize,
                                  crate::cbordetver::option__size_t::Some { v: sz } => sz,
                                  _ => panic!("Incomplete pattern matching")
                              }
                          }
                          else
                          { 0usize }
                      }
                      else
                      { 0usize }
                  }
              }
              else
              { 0usize }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Serializer for sig_structure
*/
pub fn
serialize_sig_structure(c: sig_structure, out: &mut [u8]) ->
    usize
{
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let
    _letpattern:
    (either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t_tags,
    (empty_or_serialized_map,
    either__·COSE_Format_empty_or_serialized_map····Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t··_·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·))
    =
        sig_structure_left(c);
    let res: bool =
        {
            let c1: either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t_tags =
                _letpattern.0;
            let
            c2:
            (empty_or_serialized_map,
            either__·COSE_Format_empty_or_serialized_map····Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t··_·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·)
            =
                _letpattern.1;
            let count: u64 = (&pcount)[0usize];
            let res1: bool =
                if count < 18446744073709551615u64
                {
                    let size: usize = (&psize)[0usize];
                    let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                    let _out0: &[u8] = _letpattern1.0;
                    let out1: &mut [u8] = _letpattern1.1;
                    let size1: usize =
                        match c1
                        {
                            either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t_tags::Inl
                            =>
                              {
                                  let mut a: Box<[u8]> =
                                      vec![0u8; 9u64 as usize].into_boxed_slice();
                                  let len_sz: usize = 9u64 as usize;
                                  let s: &mut [u8] = &mut a;
                                  s[0usize] = 83u8;
                                  let i·: usize = 1usize;
                                  s[i·] = 105u8;
                                  let i·1: usize = i·.wrapping_add(1usize);
                                  s[i·1] = 103u8;
                                  let i·2: usize = i·1.wrapping_add(1usize);
                                  s[i·2] = 110u8;
                                  let i·3: usize = i·2.wrapping_add(1usize);
                                  s[i·3] = 97u8;
                                  let i·4: usize = i·3.wrapping_add(1usize);
                                  s[i·4] = 116u8;
                                  let i·5: usize = i·4.wrapping_add(1usize);
                                  s[i·5] = 117u8;
                                  let i·6: usize = i·5.wrapping_add(1usize);
                                  s[i·6] = 114u8;
                                  let i·7: usize = i·6.wrapping_add(1usize);
                                  s[i·7] = 101u8;
                                  let mty: crate::cbordetver::cbor_det_string_kind =
                                      if
                                      crate::cbordetveraux::cbor_major_type_text_string
                                      ==
                                      crate::cbordetveraux::cbor_major_type_byte_string
                                      { crate::cbordetver::cbor_det_string_kind::ByteString }
                                      else
                                      { crate::cbordetver::cbor_det_string_kind::TextString };
                                  let res: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                                      crate::cbordetver::cbor_det_mk_string(mty, s);
                                  let c3: crate::cbordetveraux::cbor_raw =
                                      match res
                                      {
                                          crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                          { v: c3 }
                                          => c3,
                                          _ => panic!("Incomplete pattern matching")
                                      };
                                  let res1: crate::cbordetver::option__size_t =
                                      crate::cbordetver::cbor_det_serialize(c3, out1);
                                  match res1
                                  {
                                      crate::cbordetver::option__size_t::None => 0usize,
                                      crate::cbordetver::option__size_t::Some { v: r } => r,
                                      _ => panic!("Incomplete pattern matching")
                                  }
                              },
                            either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t_tags::Inr
                            =>
                              {
                                  let mut a: Box<[u8]> =
                                      vec![0u8; 10u64 as usize].into_boxed_slice();
                                  let len_sz: usize = 10u64 as usize;
                                  let s: &mut [u8] = &mut a;
                                  s[0usize] = 83u8;
                                  let i·: usize = 1usize;
                                  s[i·] = 105u8;
                                  let i·1: usize = i·.wrapping_add(1usize);
                                  s[i·1] = 103u8;
                                  let i·2: usize = i·1.wrapping_add(1usize);
                                  s[i·2] = 110u8;
                                  let i·3: usize = i·2.wrapping_add(1usize);
                                  s[i·3] = 97u8;
                                  let i·4: usize = i·3.wrapping_add(1usize);
                                  s[i·4] = 116u8;
                                  let i·5: usize = i·4.wrapping_add(1usize);
                                  s[i·5] = 117u8;
                                  let i·6: usize = i·5.wrapping_add(1usize);
                                  s[i·6] = 114u8;
                                  let i·7: usize = i·6.wrapping_add(1usize);
                                  s[i·7] = 101u8;
                                  let i·8: usize = i·7.wrapping_add(1usize);
                                  s[i·8] = 49u8;
                                  let mty: crate::cbordetver::cbor_det_string_kind =
                                      if
                                      crate::cbordetveraux::cbor_major_type_text_string
                                      ==
                                      crate::cbordetveraux::cbor_major_type_byte_string
                                      { crate::cbordetver::cbor_det_string_kind::ByteString }
                                      else
                                      { crate::cbordetver::cbor_det_string_kind::TextString };
                                  let res: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                                      crate::cbordetver::cbor_det_mk_string(mty, s);
                                  let c3: crate::cbordetveraux::cbor_raw =
                                      match res
                                      {
                                          crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                          { v: c3 }
                                          => c3,
                                          _ => panic!("Incomplete pattern matching")
                                      };
                                  let res1: crate::cbordetver::option__size_t =
                                      crate::cbordetver::cbor_det_serialize(c3, out1);
                                  match res1
                                  {
                                      crate::cbordetver::option__size_t::None => 0usize,
                                      crate::cbordetver::option__size_t::Some { v: r } => r,
                                      _ => panic!("Incomplete pattern matching")
                                  }
                              },
                            _ => panic!("Precondition of the function most likely violated")
                        };
                    if size1 == 0usize
                    { false }
                    else
                    {
                        (&mut pcount)[0usize] = count.wrapping_add(1u64);
                        (&mut psize)[0usize] = size.wrapping_add(size1);
                        true
                    }
                }
                else
                { false };
            if res1
            {
                let c11: empty_or_serialized_map = c2.0;
                let
                c21:
                either__·COSE_Format_empty_or_serialized_map····Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t··_·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·
                =
                    c2.1;
                let count1: u64 = (&pcount)[0usize];
                let res11: bool =
                    if count1 < 18446744073709551615u64
                    {
                        let size: usize = (&psize)[0usize];
                        let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                        let _out0: &[u8] = _letpattern1.0;
                        let out1: &mut [u8] = _letpattern1.1;
                        let size1: usize = serialize_empty_or_serialized_map(c11, out1);
                        if size1 == 0usize
                        { false }
                        else
                        {
                            (&mut pcount)[0usize] = count1.wrapping_add(1u64);
                            (&mut psize)[0usize] = size.wrapping_add(size1);
                            true
                        }
                    }
                    else
                    { false };
                if res11
                {
                    match c21
                    {
                        either__·COSE_Format_empty_or_serialized_map····Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t··_·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::Inl
                        { v: c12 }
                        =>
                          {
                              let c13: empty_or_serialized_map = c12.0;
                              let c22: (&[u8], &[u8]) = c12.1;
                              let count2: u64 = (&pcount)[0usize];
                              let res12: bool =
                                  if count2 < 18446744073709551615u64
                                  {
                                      let size: usize = (&psize)[0usize];
                                      let _letpattern1: (&mut [u8], &mut [u8]) =
                                          out.split_at_mut(size);
                                      let _out0: &[u8] = _letpattern1.0;
                                      let out1: &mut [u8] = _letpattern1.1;
                                      let size1: usize =
                                          serialize_empty_or_serialized_map(c13, out1);
                                      if size1 == 0usize
                                      { false }
                                      else
                                      {
                                          (&mut pcount)[0usize] = count2.wrapping_add(1u64);
                                          (&mut psize)[0usize] = size.wrapping_add(size1);
                                          true
                                      }
                                  }
                                  else
                                  { false };
                              if res12
                              {
                                  let c14: &[u8] = c22.0;
                                  let c23: &[u8] = c22.1;
                                  let count3: u64 = (&pcount)[0usize];
                                  let res13: bool =
                                      if count3 < 18446744073709551615u64
                                      {
                                          let size: usize = (&psize)[0usize];
                                          let _letpattern1: (&mut [u8], &mut [u8]) =
                                              out.split_at_mut(size);
                                          let _out0: &[u8] = _letpattern1.0;
                                          let out1: &mut [u8] = _letpattern1.1;
                                          let size1: usize = serialize_bstr(c14, out1);
                                          if size1 == 0usize
                                          { false }
                                          else
                                          {
                                              (&mut pcount)[0usize] = count3.wrapping_add(1u64);
                                              (&mut psize)[0usize] = size.wrapping_add(size1);
                                              true
                                          }
                                      }
                                      else
                                      { false };
                                  if res13
                                  {
                                      let count4: u64 = (&pcount)[0usize];
                                      if count4 < 18446744073709551615u64
                                      {
                                          let size: usize = (&psize)[0usize];
                                          let _letpattern1: (&mut [u8], &mut [u8]) =
                                              out.split_at_mut(size);
                                          let _out0: &[u8] = _letpattern1.0;
                                          let out1: &mut [u8] = _letpattern1.1;
                                          let size1: usize = serialize_bstr(c23, out1);
                                          if size1 == 0usize
                                          { false }
                                          else
                                          {
                                              (&mut pcount)[0usize] = count4.wrapping_add(1u64);
                                              (&mut psize)[0usize] = size.wrapping_add(size1);
                                              true
                                          }
                                      }
                                      else
                                      { false }
                                  }
                                  else
                                  { false }
                              }
                              else
                              { false }
                          },
                        either__·COSE_Format_empty_or_serialized_map····Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t··_·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::Inr
                        { v: c22 }
                        =>
                          {
                              let c12: &[u8] = c22.0;
                              let c23: &[u8] = c22.1;
                              let count2: u64 = (&pcount)[0usize];
                              let res12: bool =
                                  if count2 < 18446744073709551615u64
                                  {
                                      let size: usize = (&psize)[0usize];
                                      let _letpattern1: (&mut [u8], &mut [u8]) =
                                          out.split_at_mut(size);
                                      let _out0: &[u8] = _letpattern1.0;
                                      let out1: &mut [u8] = _letpattern1.1;
                                      let size1: usize = serialize_bstr(c12, out1);
                                      if size1 == 0usize
                                      { false }
                                      else
                                      {
                                          (&mut pcount)[0usize] = count2.wrapping_add(1u64);
                                          (&mut psize)[0usize] = size.wrapping_add(size1);
                                          true
                                      }
                                  }
                                  else
                                  { false };
                              if res12
                              {
                                  let count3: u64 = (&pcount)[0usize];
                                  if count3 < 18446744073709551615u64
                                  {
                                      let size: usize = (&psize)[0usize];
                                      let _letpattern1: (&mut [u8], &mut [u8]) =
                                          out.split_at_mut(size);
                                      let _out0: &[u8] = _letpattern1.0;
                                      let out1: &mut [u8] = _letpattern1.1;
                                      let size1: usize = serialize_bstr(c23, out1);
                                      if size1 == 0usize
                                      { false }
                                      else
                                      {
                                          (&mut pcount)[0usize] = count3.wrapping_add(1u64);
                                          (&mut psize)[0usize] = size.wrapping_add(size1);
                                          true
                                      }
                                  }
                                  else
                                  { false }
                              }
                              else
                              { false }
                          },
                        _ => panic!("Incomplete pattern matching")
                    }
                }
                else
                { false }
            }
            else
            { false }
        };
    if res
    {
        let size: usize = (&psize)[0usize];
        let count: u64 = (&pcount)[0usize];
        crate::cbordetver::cbor_det_serialize_array(count, out, size)
    }
    else
    { 0usize }
}

#[derive(PartialEq, Clone, Copy)]
pub enum either__Pulse_Lib_Slice_slice·uint8_t_·· <'a>
{
    Inl { v: &'a [u8] },
    Inr
}

#[derive(PartialEq, Clone, Copy)]
pub struct cose_sign1 <'a>
{
    pub protected: empty_or_serialized_map <'a>,
    pub unprotected: header_map <'a>,
    pub payload: either__Pulse_Lib_Slice_slice·uint8_t_·· <'a>,
    pub signature: &'a [u8]
}

pub type cose_sign1_tagged <'a> = cose_sign1 <'a>;

pub type cose_sign1_tagged_ugly <'a> = cose_sign1 <'a>;

pub fn cose_sign1_tagged_left <'a>(x4: cose_sign1 <'a>) -> cose_sign1 <'a> { x4 }

pub fn cose_sign1_left <'a>(x10: cose_sign1 <'a>) ->
    ((empty_or_serialized_map <'a>, header_map <'a>),
    (either__Pulse_Lib_Slice_slice·uint8_t_·· <'a>, &'a [u8]))
{ ((x10.protected,x10.unprotected),(x10.payload,x10.signature)) }

/**
Serializer for nil
*/
pub fn
serialize_nil(out: &mut [u8]) ->
    usize
{
    let _letpattern: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_mk_simple_value(22u8);
    let c1: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res } => res,
            _ => panic!("Incomplete pattern matching")
        };
    let res: crate::cbordetver::option__size_t = crate::cbordetver::cbor_det_serialize(c1, out);
    match res
    {
        crate::cbordetver::option__size_t::None => 0usize,
        crate::cbordetver::option__size_t::Some { v: r } => r,
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Serializer for cose_sign1
*/
pub fn
serialize_cose_sign1(c: cose_sign1, out: &mut [u8]) ->
    usize
{
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let
    _letpattern:
    ((empty_or_serialized_map, header_map), (either__Pulse_Lib_Slice_slice·uint8_t_··, &[u8]))
    =
        cose_sign1_left(c);
    let res: bool =
        {
            let c1: (empty_or_serialized_map, header_map) = _letpattern.0;
            let c2: (either__Pulse_Lib_Slice_slice·uint8_t_··, &[u8]) = _letpattern.1;
            let res1: bool =
                {
                    let c11: empty_or_serialized_map = c1.0;
                    let c21: header_map = c1.1;
                    let count: u64 = (&pcount)[0usize];
                    let res1: bool =
                        if count < 18446744073709551615u64
                        {
                            let size: usize = (&psize)[0usize];
                            let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                            let _out0: &[u8] = _letpattern1.0;
                            let out1: &mut [u8] = _letpattern1.1;
                            let size1: usize = serialize_empty_or_serialized_map(c11, out1);
                            if size1 == 0usize
                            { false }
                            else
                            {
                                (&mut pcount)[0usize] = count.wrapping_add(1u64);
                                (&mut psize)[0usize] = size.wrapping_add(size1);
                                true
                            }
                        }
                        else
                        { false };
                    if res1
                    {
                        let count1: u64 = (&pcount)[0usize];
                        if count1 < 18446744073709551615u64
                        {
                            let size: usize = (&psize)[0usize];
                            let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                            let _out0: &[u8] = _letpattern1.0;
                            let out1: &mut [u8] = _letpattern1.1;
                            let size1: usize = serialize_header_map(c21, out1);
                            if size1 == 0usize
                            { false }
                            else
                            {
                                (&mut pcount)[0usize] = count1.wrapping_add(1u64);
                                (&mut psize)[0usize] = size.wrapping_add(size1);
                                true
                            }
                        }
                        else
                        { false }
                    }
                    else
                    { false }
                };
            if res1
            {
                let c11: either__Pulse_Lib_Slice_slice·uint8_t_·· = c2.0;
                let c21: &[u8] = c2.1;
                let count: u64 = (&pcount)[0usize];
                let res11: bool =
                    if count < 18446744073709551615u64
                    {
                        let size: usize = (&psize)[0usize];
                        let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                        let _out0: &[u8] = _letpattern1.0;
                        let out1: &mut [u8] = _letpattern1.1;
                        let size1: usize =
                            match c11
                            {
                                either__Pulse_Lib_Slice_slice·uint8_t_··::Inl { v: c12 } =>
                                  serialize_bstr(c12, out1),
                                either__Pulse_Lib_Slice_slice·uint8_t_··::Inr =>
                                  serialize_nil(out1),
                                _ => panic!("Incomplete pattern matching")
                            };
                        if size1 == 0usize
                        { false }
                        else
                        {
                            (&mut pcount)[0usize] = count.wrapping_add(1u64);
                            (&mut psize)[0usize] = size.wrapping_add(size1);
                            true
                        }
                    }
                    else
                    { false };
                if res11
                {
                    let count1: u64 = (&pcount)[0usize];
                    if count1 < 18446744073709551615u64
                    {
                        let size: usize = (&psize)[0usize];
                        let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                        let _out0: &[u8] = _letpattern1.0;
                        let out1: &mut [u8] = _letpattern1.1;
                        let size1: usize = serialize_bstr(c21, out1);
                        if size1 == 0usize
                        { false }
                        else
                        {
                            (&mut pcount)[0usize] = count1.wrapping_add(1u64);
                            (&mut psize)[0usize] = size.wrapping_add(size1);
                            true
                        }
                    }
                    else
                    { false }
                }
                else
                { false }
            }
            else
            { false }
        };
    if res
    {
        let size: usize = (&psize)[0usize];
        let count: u64 = (&pcount)[0usize];
        crate::cbordetver::cbor_det_serialize_array(count, out, size)
    }
    else
    { 0usize }
}

/**
Serializer for cose_sign1_tagged
*/
pub fn
serialize_cose_sign1_tagged(c: cose_sign1, out: &mut [u8]) ->
    usize
{
    let c·: (u64, cose_sign1) = (18u64,c);
    let ctag: u64 = c·.0;
    let cpayload: cose_sign1 = c·.1;
    let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
    if tsz == 0usize
    { 0usize }
    else
    {
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
        let _tmp: &[u8] = _letpattern.0;
        let out2: &mut [u8] = _letpattern.1;
        let psz: usize = serialize_cose_sign1(cpayload, out2);
        if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
    }
}

pub type spect_evercddl_uint = u64;

pub type spect_nint = u64;

pub fn validate_everparsenomatch(c: crate::cbordetveraux::cbor_raw) -> bool
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    false
}

pub fn validate_any(c: crate::cbordetveraux::cbor_raw) -> bool
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    true
}

pub fn validate_values(c: crate::cbordetveraux::cbor_raw) -> bool { validate_any(c) }

pub fn validate_header_map(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let ty: u8 = crate::cbordetver::cbor_det_major_type(c);
    if ty == crate::cbordetveraux::cbor_major_type_map
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let rem0: u64 =
            match v
            {
                crate::cbordetver::cbor_det_view::Map { _0: a } =>
                  crate::cbordetver::cbor_det_map_length(a),
                _ => panic!("Incomplete pattern matching")
            };
        let mut remaining: [u64; 1] = [rem0; 1usize];
        let i0: u64 = (&remaining)[0usize];
        let mty: crate::cbordetver::cbor_det_int_kind =
            crate::cbordetver::cbor_det_int_kind::UInt64;
        let c1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty, 1u64);
        let x·: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let mg: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
            match x·
            {
                crate::cbordetver::cbor_det_view::Map { _0: m } =>
                  crate::cbordetver::cbor_det_map_get(m, c1),
                _ => panic!("Incomplete pattern matching")
            };
        let res1: crate::cbordetveraux::impl_map_group_result =
            match mg
            {
                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: cv } =>
                  {
                      let test: bool = validate_int(cv);
                      let check_value: bool = if test { true } else { validate_tstr(cv) };
                      if check_value
                      {
                          let i1: u64 = (&remaining)[0usize];
                          let i2: u64 = i1.wrapping_sub(1u64);
                          (&mut remaining)[0usize] = i2;
                          crate::cbordetveraux::impl_map_group_result::MGOK
                      }
                      else
                      { crate::cbordetveraux::impl_map_group_result::MGFail }
                  },
                _ => panic!("Incomplete pattern matching")
            };
        let res11: crate::cbordetveraux::impl_map_group_result =
            match res1
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  crate::cbordetveraux::impl_map_group_result::MGOK,
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  {
                      (&mut remaining)[0usize] = i0;
                      crate::cbordetveraux::impl_map_group_result::MGOK
                  },
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        let res12: crate::cbordetveraux::impl_map_group_result =
            match res11
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  {
                      let i01: u64 = (&remaining)[0usize];
                      let mty1: crate::cbordetver::cbor_det_int_kind =
                          crate::cbordetver::cbor_det_int_kind::UInt64;
                      let c2: crate::cbordetveraux::cbor_raw =
                          crate::cbordetver::cbor_det_mk_int64(mty1, 2u64);
                      let x·1: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let mg1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                          match x·1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: m } =>
                                crate::cbordetver::cbor_det_map_get(m, c2),
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res12: crate::cbordetveraux::impl_map_group_result =
                          match mg1
                          {
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                                crate::cbordetveraux::impl_map_group_result::MGFail,
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                              { v: cv }
                              =>
                                {
                                    let ty1: u8 = crate::cbordetver::cbor_det_major_type(cv);
                                    let check_value: bool =
                                        if ty1 == crate::cbordetveraux::cbor_major_type_array
                                        {
                                            let v1: crate::cbordetver::cbor_det_view =
                                                crate::cbordetver::cbor_det_destruct(cv);
                                            let
                                            i:
                                            crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                            =
                                                match v1
                                                {
                                                    crate::cbordetver::cbor_det_view::Array
                                                    { _0: a }
                                                    =>
                                                      crate::cbordetver::cbor_det_array_iterator_start(
                                                          a
                                                      ),
                                                    _ => panic!("Incomplete pattern matching")
                                                };
                                            let
                                            mut
                                            pi:
                                            [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw;
                                            1]
                                            =
                                                [i; 1usize];
                                            let
                                            i1:
                                            crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                            =
                                                (&pi)[0usize];
                                            let is_done: bool =
                                                crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                    i1
                                                );
                                            let test1: bool =
                                                if is_done
                                                { false }
                                                else
                                                {
                                                    let c3: crate::cbordetveraux::cbor_raw =
                                                        crate::cbordetver::cbor_det_array_iterator_next(
                                                            &mut pi
                                                        );
                                                    validate_evercddl_label(c3)
                                                };
                                            let b_success: bool =
                                                if test1
                                                {
                                                    let mut pcont: [bool; 1] = [true; 1usize];
                                                    while
                                                    (&pcont)[0usize]
                                                    {
                                                        let
                                                        i11:
                                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                        =
                                                            (&pi)[0usize];
                                                        let
                                                        i2:
                                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                        =
                                                            (&pi)[0usize];
                                                        let is_done1: bool =
                                                            crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                                i2
                                                            );
                                                        let cont: bool =
                                                            if is_done1
                                                            { false }
                                                            else
                                                            {
                                                                let
                                                                c3: crate::cbordetveraux::cbor_raw
                                                                =
                                                                    crate::cbordetver::cbor_det_array_iterator_next(
                                                                        &mut pi
                                                                    );
                                                                validate_evercddl_label(c3)
                                                            };
                                                        if ! cont
                                                        {
                                                            (&mut pi)[0usize] = i11;
                                                            (&mut pcont)[0usize] = false
                                                        }
                                                    };
                                                    true
                                                }
                                                else
                                                { false };
                                            if b_success
                                            {
                                                let
                                                i·:
                                                crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                =
                                                    (&pi)[0usize];
                                                crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                    i·
                                                )
                                            }
                                            else
                                            { false }
                                        }
                                        else
                                        { false };
                                    if check_value
                                    {
                                        let i1: u64 = (&remaining)[0usize];
                                        let i2: u64 = i1.wrapping_sub(1u64);
                                        (&mut remaining)[0usize] = i2;
                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                    }
                                    else
                                    { crate::cbordetveraux::impl_map_group_result::MGFail }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      match res12
                      {
                          crate::cbordetveraux::impl_map_group_result::MGOK =>
                            crate::cbordetveraux::impl_map_group_result::MGOK,
                          crate::cbordetveraux::impl_map_group_result::MGFail =>
                            {
                                (&mut remaining)[0usize] = i01;
                                crate::cbordetveraux::impl_map_group_result::MGOK
                            },
                          crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                            crate::cbordetveraux::impl_map_group_result::MGCutFail,
                          _ => panic!("Precondition of the function most likely violated")
                      }
                  },
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        let res13: crate::cbordetveraux::impl_map_group_result =
            match res12
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  {
                      let i01: u64 = (&remaining)[0usize];
                      let mty1: crate::cbordetver::cbor_det_int_kind =
                          crate::cbordetver::cbor_det_int_kind::UInt64;
                      let c2: crate::cbordetveraux::cbor_raw =
                          crate::cbordetver::cbor_det_mk_int64(mty1, 3u64);
                      let x·1: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let mg1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                          match x·1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: m } =>
                                crate::cbordetver::cbor_det_map_get(m, c2),
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res13: crate::cbordetveraux::impl_map_group_result =
                          match mg1
                          {
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                                crate::cbordetveraux::impl_map_group_result::MGFail,
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                              { v: cv }
                              =>
                                {
                                    let test: bool = validate_tstr(cv);
                                    let check_value: bool =
                                        if test { true } else { validate_int(cv) };
                                    if check_value
                                    {
                                        let i1: u64 = (&remaining)[0usize];
                                        let i2: u64 = i1.wrapping_sub(1u64);
                                        (&mut remaining)[0usize] = i2;
                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                    }
                                    else
                                    { crate::cbordetveraux::impl_map_group_result::MGFail }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      match res13
                      {
                          crate::cbordetveraux::impl_map_group_result::MGOK =>
                            crate::cbordetveraux::impl_map_group_result::MGOK,
                          crate::cbordetveraux::impl_map_group_result::MGFail =>
                            {
                                (&mut remaining)[0usize] = i01;
                                crate::cbordetveraux::impl_map_group_result::MGOK
                            },
                          crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                            crate::cbordetveraux::impl_map_group_result::MGCutFail,
                          _ => panic!("Precondition of the function most likely violated")
                      }
                  },
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        let res14: crate::cbordetveraux::impl_map_group_result =
            match res13
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  {
                      let i01: u64 = (&remaining)[0usize];
                      let mty1: crate::cbordetver::cbor_det_int_kind =
                          crate::cbordetver::cbor_det_int_kind::UInt64;
                      let c2: crate::cbordetveraux::cbor_raw =
                          crate::cbordetver::cbor_det_mk_int64(mty1, 4u64);
                      let x·1: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let mg1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                          match x·1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: m } =>
                                crate::cbordetver::cbor_det_map_get(m, c2),
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res14: crate::cbordetveraux::impl_map_group_result =
                          match mg1
                          {
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                                crate::cbordetveraux::impl_map_group_result::MGFail,
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                              { v: cv }
                              =>
                                {
                                    let check_value: bool = validate_bstr(cv);
                                    if check_value
                                    {
                                        let i1: u64 = (&remaining)[0usize];
                                        let i2: u64 = i1.wrapping_sub(1u64);
                                        (&mut remaining)[0usize] = i2;
                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                    }
                                    else
                                    { crate::cbordetveraux::impl_map_group_result::MGFail }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      match res14
                      {
                          crate::cbordetveraux::impl_map_group_result::MGOK =>
                            crate::cbordetveraux::impl_map_group_result::MGOK,
                          crate::cbordetveraux::impl_map_group_result::MGFail =>
                            {
                                (&mut remaining)[0usize] = i01;
                                crate::cbordetveraux::impl_map_group_result::MGOK
                            },
                          crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                            crate::cbordetveraux::impl_map_group_result::MGCutFail,
                          _ => panic!("Precondition of the function most likely violated")
                      }
                  },
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        let res15: crate::cbordetveraux::impl_map_group_result =
            match res14
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  {
                      let i01: u64 = (&remaining)[0usize];
                      let mty1: crate::cbordetver::cbor_det_int_kind =
                          crate::cbordetver::cbor_det_int_kind::UInt64;
                      let c2: crate::cbordetveraux::cbor_raw =
                          crate::cbordetver::cbor_det_mk_int64(mty1, 5u64);
                      let x·1: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let mg1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                          match x·1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: m } =>
                                crate::cbordetver::cbor_det_map_get(m, c2),
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res15: crate::cbordetveraux::impl_map_group_result =
                          match mg1
                          {
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                                crate::cbordetveraux::impl_map_group_result::MGFail,
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                              { v: cv }
                              =>
                                {
                                    let check_value: bool = validate_bstr(cv);
                                    if check_value
                                    {
                                        let i1: u64 = (&remaining)[0usize];
                                        let i2: u64 = i1.wrapping_sub(1u64);
                                        (&mut remaining)[0usize] = i2;
                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                    }
                                    else
                                    { crate::cbordetveraux::impl_map_group_result::MGFail }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res16: crate::cbordetveraux::impl_map_group_result =
                          match res15
                          {
                              crate::cbordetveraux::impl_map_group_result::MGOK =>
                                {
                                    let i02: u64 = (&remaining)[0usize];
                                    let mty2: crate::cbordetver::cbor_det_int_kind =
                                        crate::cbordetver::cbor_det_int_kind::UInt64;
                                    let c3: crate::cbordetveraux::cbor_raw =
                                        crate::cbordetver::cbor_det_mk_int64(mty2, 6u64);
                                    let x·2: crate::cbordetver::cbor_det_view =
                                        crate::cbordetver::cbor_det_destruct(c);
                                    let
                                    mg2: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                    =
                                        match x·2
                                        {
                                            crate::cbordetver::cbor_det_view::Map { _0: m } =>
                                              crate::cbordetver::cbor_det_map_get(m, c3),
                                            _ => panic!("Incomplete pattern matching")
                                        };
                                    let res16: crate::cbordetveraux::impl_map_group_result =
                                        match mg2
                                        {
                                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None
                                            => crate::cbordetveraux::impl_map_group_result::MGFail,
                                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                            { v: cv }
                                            =>
                                              {
                                                  let check_value: bool =
                                                      validate_everparsenomatch(cv);
                                                  if check_value
                                                  {
                                                      let i1: u64 = (&remaining)[0usize];
                                                      let i2: u64 = i1.wrapping_sub(1u64);
                                                      (&mut remaining)[0usize] = i2;
                                                      crate::cbordetveraux::impl_map_group_result::MGOK
                                                  }
                                                  else
                                                  {
                                                      crate::cbordetveraux::impl_map_group_result::MGCutFail
                                                  }
                                              },
                                            _ => panic!("Incomplete pattern matching")
                                        };
                                    match res16
                                    {
                                        crate::cbordetveraux::impl_map_group_result::MGOK =>
                                          crate::cbordetveraux::impl_map_group_result::MGOK,
                                        crate::cbordetveraux::impl_map_group_result::MGFail =>
                                          {
                                              (&mut remaining)[0usize] = i02;
                                              crate::cbordetveraux::impl_map_group_result::MGOK
                                          },
                                        crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                                          crate::cbordetveraux::impl_map_group_result::MGCutFail,
                                        _ =>
                                          panic!(
                                              "Precondition of the function most likely violated"
                                          )
                                    }
                                },
                              crate::cbordetveraux::impl_map_group_result::MGFail =>
                                crate::cbordetveraux::impl_map_group_result::MGFail,
                              crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                                crate::cbordetveraux::impl_map_group_result::MGCutFail,
                              _ => panic!("Precondition of the function most likely violated")
                          };
                      match res16
                      {
                          crate::cbordetveraux::impl_map_group_result::MGOK =>
                            crate::cbordetveraux::impl_map_group_result::MGOK,
                          crate::cbordetveraux::impl_map_group_result::MGFail =>
                            {
                                (&mut remaining)[0usize] = i01;
                                let i02: u64 = (&remaining)[0usize];
                                let mty2: crate::cbordetver::cbor_det_int_kind =
                                    crate::cbordetver::cbor_det_int_kind::UInt64;
                                let c3: crate::cbordetveraux::cbor_raw =
                                    crate::cbordetver::cbor_det_mk_int64(mty2, 6u64);
                                let x·2: crate::cbordetver::cbor_det_view =
                                    crate::cbordetver::cbor_det_destruct(c);
                                let mg2: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                                    match x·2
                                    {
                                        crate::cbordetver::cbor_det_view::Map { _0: m } =>
                                          crate::cbordetver::cbor_det_map_get(m, c3),
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                let res17: crate::cbordetveraux::impl_map_group_result =
                                    match mg2
                                    {
                                        crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None
                                        => crate::cbordetveraux::impl_map_group_result::MGFail,
                                        crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                        { v: cv }
                                        =>
                                          {
                                              let check_value: bool = validate_bstr(cv);
                                              if check_value
                                              {
                                                  let i1: u64 = (&remaining)[0usize];
                                                  let i2: u64 = i1.wrapping_sub(1u64);
                                                  (&mut remaining)[0usize] = i2;
                                                  crate::cbordetveraux::impl_map_group_result::MGOK
                                              }
                                              else
                                              {
                                                  crate::cbordetveraux::impl_map_group_result::MGFail
                                              }
                                          },
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                let res18: crate::cbordetveraux::impl_map_group_result =
                                    match res17
                                    {
                                        crate::cbordetveraux::impl_map_group_result::MGOK =>
                                          {
                                              let i03: u64 = (&remaining)[0usize];
                                              let mty3: crate::cbordetver::cbor_det_int_kind =
                                                  crate::cbordetver::cbor_det_int_kind::UInt64;
                                              let c4: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_mk_int64(mty3, 5u64);
                                              let x·3: crate::cbordetver::cbor_det_view =
                                                  crate::cbordetver::cbor_det_destruct(c);
                                              let
                                              mg3:
                                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                              =
                                                  match x·3
                                                  {
                                                      crate::cbordetver::cbor_det_view::Map
                                                      { _0: m }
                                                      => crate::cbordetver::cbor_det_map_get(m, c4),
                                                      _ => panic!("Incomplete pattern matching")
                                                  };
                                              let
                                              res18: crate::cbordetveraux::impl_map_group_result
                                              =
                                                  match mg3
                                                  {
                                                      crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None
                                                      =>
                                                        crate::cbordetveraux::impl_map_group_result::MGFail,
                                                      crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                      { v: cv }
                                                      =>
                                                        {
                                                            let check_value: bool =
                                                                validate_everparsenomatch(cv);
                                                            if check_value
                                                            {
                                                                let i1: u64 = (&remaining)[0usize];
                                                                let i2: u64 = i1.wrapping_sub(1u64);
                                                                (&mut remaining)[0usize] = i2;
                                                                crate::cbordetveraux::impl_map_group_result::MGOK
                                                            }
                                                            else
                                                            {
                                                                crate::cbordetveraux::impl_map_group_result::MGCutFail
                                                            }
                                                        },
                                                      _ => panic!("Incomplete pattern matching")
                                                  };
                                              match res18
                                              {
                                                  crate::cbordetveraux::impl_map_group_result::MGOK
                                                  =>
                                                    crate::cbordetveraux::impl_map_group_result::MGOK,
                                                  crate::cbordetveraux::impl_map_group_result::MGFail
                                                  =>
                                                    {
                                                        (&mut remaining)[0usize] = i03;
                                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                                    },
                                                  crate::cbordetveraux::impl_map_group_result::MGCutFail
                                                  =>
                                                    crate::cbordetveraux::impl_map_group_result::MGCutFail,
                                                  _ =>
                                                    panic!(
                                                        "Precondition of the function most likely violated"
                                                    )
                                              }
                                          },
                                        crate::cbordetveraux::impl_map_group_result::MGFail =>
                                          crate::cbordetveraux::impl_map_group_result::MGFail,
                                        crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                                          crate::cbordetveraux::impl_map_group_result::MGCutFail,
                                        _ =>
                                          panic!(
                                              "Precondition of the function most likely violated"
                                          )
                                    };
                                match res18
                                {
                                    crate::cbordetveraux::impl_map_group_result::MGOK =>
                                      crate::cbordetveraux::impl_map_group_result::MGOK,
                                    crate::cbordetveraux::impl_map_group_result::MGFail =>
                                      {
                                          (&mut remaining)[0usize] = i02;
                                          let i03: u64 = (&remaining)[0usize];
                                          let mty3: crate::cbordetver::cbor_det_int_kind =
                                              crate::cbordetver::cbor_det_int_kind::UInt64;
                                          let c4: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_mk_int64(mty3, 6u64);
                                          let x·3: crate::cbordetver::cbor_det_view =
                                              crate::cbordetver::cbor_det_destruct(c);
                                          let
                                          mg3:
                                          crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                          =
                                              match x·3
                                              {
                                                  crate::cbordetver::cbor_det_view::Map { _0: m } =>
                                                    crate::cbordetver::cbor_det_map_get(m, c4),
                                                  _ => panic!("Incomplete pattern matching")
                                              };
                                          let res19: crate::cbordetveraux::impl_map_group_result =
                                              match mg3
                                              {
                                                  crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None
                                                  =>
                                                    crate::cbordetveraux::impl_map_group_result::MGFail,
                                                  crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                  { v: cv }
                                                  =>
                                                    {
                                                        let check_value: bool =
                                                            validate_everparsenomatch(cv);
                                                        if check_value
                                                        {
                                                            let i1: u64 = (&remaining)[0usize];
                                                            let i2: u64 = i1.wrapping_sub(1u64);
                                                            (&mut remaining)[0usize] = i2;
                                                            crate::cbordetveraux::impl_map_group_result::MGOK
                                                        }
                                                        else
                                                        {
                                                            crate::cbordetveraux::impl_map_group_result::MGCutFail
                                                        }
                                                    },
                                                  _ => panic!("Incomplete pattern matching")
                                              };
                                          let res110: crate::cbordetveraux::impl_map_group_result =
                                              match res19
                                              {
                                                  crate::cbordetveraux::impl_map_group_result::MGOK
                                                  =>
                                                    crate::cbordetveraux::impl_map_group_result::MGOK,
                                                  crate::cbordetveraux::impl_map_group_result::MGFail
                                                  =>
                                                    {
                                                        (&mut remaining)[0usize] = i03;
                                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                                    },
                                                  crate::cbordetveraux::impl_map_group_result::MGCutFail
                                                  =>
                                                    crate::cbordetveraux::impl_map_group_result::MGCutFail,
                                                  _ =>
                                                    panic!(
                                                        "Precondition of the function most likely violated"
                                                    )
                                              };
                                          match res110
                                          {
                                              crate::cbordetveraux::impl_map_group_result::MGOK =>
                                                {
                                                    let i04: u64 = (&remaining)[0usize];
                                                    let mty4: crate::cbordetver::cbor_det_int_kind =
                                                        crate::cbordetver::cbor_det_int_kind::UInt64;
                                                    let c5: crate::cbordetveraux::cbor_raw =
                                                        crate::cbordetver::cbor_det_mk_int64(
                                                            mty4,
                                                            5u64
                                                        );
                                                    let x·4: crate::cbordetver::cbor_det_view =
                                                        crate::cbordetver::cbor_det_destruct(c);
                                                    let
                                                    mg4:
                                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                    =
                                                        match x·4
                                                        {
                                                            crate::cbordetver::cbor_det_view::Map
                                                            { _0: m }
                                                            =>
                                                              crate::cbordetver::cbor_det_map_get(
                                                                  m,
                                                                  c5
                                                              ),
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        };
                                                    let
                                                    res111:
                                                    crate::cbordetveraux::impl_map_group_result
                                                    =
                                                        match mg4
                                                        {
                                                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None
                                                            =>
                                                              crate::cbordetveraux::impl_map_group_result::MGFail,
                                                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                            { v: cv }
                                                            =>
                                                              {
                                                                  let check_value: bool =
                                                                      validate_everparsenomatch(cv);
                                                                  if check_value
                                                                  {
                                                                      let i1: u64 =
                                                                          (&remaining)[0usize];
                                                                      let i2: u64 =
                                                                          i1.wrapping_sub(1u64);
                                                                      (&mut remaining)[0usize] = i2;
                                                                      crate::cbordetveraux::impl_map_group_result::MGOK
                                                                  }
                                                                  else
                                                                  {
                                                                      crate::cbordetveraux::impl_map_group_result::MGCutFail
                                                                  }
                                                              },
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        };
                                                    match res111
                                                    {
                                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                                        =>
                                                          crate::cbordetveraux::impl_map_group_result::MGOK,
                                                        crate::cbordetveraux::impl_map_group_result::MGFail
                                                        =>
                                                          {
                                                              (&mut remaining)[0usize] = i04;
                                                              crate::cbordetveraux::impl_map_group_result::MGOK
                                                          },
                                                        crate::cbordetveraux::impl_map_group_result::MGCutFail
                                                        =>
                                                          crate::cbordetveraux::impl_map_group_result::MGCutFail,
                                                        _ =>
                                                          panic!(
                                                              "Precondition of the function most likely violated"
                                                          )
                                                    }
                                                },
                                              crate::cbordetveraux::impl_map_group_result::MGFail =>
                                                crate::cbordetveraux::impl_map_group_result::MGFail,
                                              crate::cbordetveraux::impl_map_group_result::MGCutFail
                                              =>
                                                crate::cbordetveraux::impl_map_group_result::MGCutFail,
                                              _ =>
                                                panic!(
                                                    "Precondition of the function most likely violated"
                                                )
                                          }
                                      },
                                    crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                                      crate::cbordetveraux::impl_map_group_result::MGCutFail,
                                    _ => panic!("Precondition of the function most likely violated")
                                }
                            },
                          crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                            crate::cbordetveraux::impl_map_group_result::MGCutFail,
                          _ => panic!("Precondition of the function most likely violated")
                      }
                  },
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        let res: crate::cbordetveraux::impl_map_group_result =
            match res15
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  {
                      let v1: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let
                      j0:
                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                      =
                          match v1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: a } =>
                                crate::cbordetver::cbor_det_map_iterator_start(a),
                              _ => panic!("Incomplete pattern matching")
                          };
                      let
                      mut
                      pj:
                      [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry;
                      1]
                      =
                          [j0; 1usize];
                      let
                      j: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                      =
                          (&pj)[0usize];
                      let is_empty: bool = crate::cbordetver::cbor_det_map_iterator_is_empty(j);
                      let mut cond: bool = ! is_empty;
                      while
                      cond
                      {
                          let chd: crate::cbordetveraux::cbor_map_entry =
                              crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
                          let k: crate::cbordetveraux::cbor_raw =
                              crate::cbordetver::cbor_det_map_entry_key(chd);
                          let testk: bool = validate_evercddl_label(k);
                          let test: bool =
                              if testk
                              {
                                  let v2: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_value(chd);
                                  validate_values(v2)
                              }
                              else
                              { false };
                          let test1: bool =
                              if test
                              {
                                  let k1: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_key(chd);
                                  let mt: u8 = crate::cbordetver::cbor_det_major_type(k1);
                                  let is_uint: bool =
                                      mt == crate::cbordetveraux::cbor_major_type_uint64;
                                  let testk1: bool =
                                      if is_uint
                                      {
                                          let v2: crate::cbordetver::cbor_det_view =
                                              crate::cbordetver::cbor_det_destruct(k1);
                                          let i: u64 =
                                              match v2
                                              {
                                                  crate::cbordetver::cbor_det_view::Int64
                                                  { value: res, .. }
                                                  => res,
                                                  _ => panic!("Incomplete pattern matching")
                                              };
                                          i == 1u64
                                      }
                                      else
                                      { false };
                                  let test1: bool =
                                      if testk1
                                      {
                                          let v2: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_value(chd);
                                          let test1: bool = validate_int(v2);
                                          if test1 { true } else { validate_tstr(v2) }
                                      }
                                      else
                                      { false };
                                  let test2: bool =
                                      if test1
                                      { true }
                                      else
                                      {
                                          let k2: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(chd);
                                          let mt1: u8 = crate::cbordetver::cbor_det_major_type(k2);
                                          let is_uint1: bool =
                                              mt1 == crate::cbordetveraux::cbor_major_type_uint64;
                                          let testk2: bool =
                                              if is_uint1
                                              {
                                                  let v2: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(k2);
                                                  let i: u64 =
                                                      match v2
                                                      {
                                                          crate::cbordetver::cbor_det_view::Int64
                                                          { value: res, .. }
                                                          => res,
                                                          _ => panic!("Incomplete pattern matching")
                                                      };
                                                  i == 2u64
                                              }
                                              else
                                              { false };
                                          if testk2
                                          {
                                              let v2: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(chd);
                                              let ty1: u8 =
                                                  crate::cbordetver::cbor_det_major_type(v2);
                                              if ty1 == crate::cbordetveraux::cbor_major_type_array
                                              {
                                                  let v3: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(v2);
                                                  let
                                                  i:
                                                  crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                  =
                                                      match v3
                                                      {
                                                          crate::cbordetver::cbor_det_view::Array
                                                          { _0: a }
                                                          =>
                                                            crate::cbordetver::cbor_det_array_iterator_start(
                                                                a
                                                            ),
                                                          _ => panic!("Incomplete pattern matching")
                                                      };
                                                  let
                                                  mut
                                                  pi:
                                                  [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw;
                                                  1]
                                                  =
                                                      [i; 1usize];
                                                  let
                                                  i1:
                                                  crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                  =
                                                      (&pi)[0usize];
                                                  let is_done: bool =
                                                      crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                          i1
                                                      );
                                                  let test11: bool =
                                                      if is_done
                                                      { false }
                                                      else
                                                      {
                                                          let c2: crate::cbordetveraux::cbor_raw =
                                                              crate::cbordetver::cbor_det_array_iterator_next(
                                                                  &mut pi
                                                              );
                                                          validate_evercddl_label(c2)
                                                      };
                                                  let b_success: bool =
                                                      if test11
                                                      {
                                                          let mut pcont: [bool; 1] = [true; 1usize];
                                                          while
                                                          (&pcont)[0usize]
                                                          {
                                                              let
                                                              i11:
                                                              crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                              =
                                                                  (&pi)[0usize];
                                                              let
                                                              i2:
                                                              crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                              =
                                                                  (&pi)[0usize];
                                                              let is_done1: bool =
                                                                  crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                                      i2
                                                                  );
                                                              let cont: bool =
                                                                  if is_done1
                                                                  { false }
                                                                  else
                                                                  {
                                                                      let
                                                                      c2:
                                                                      crate::cbordetveraux::cbor_raw
                                                                      =
                                                                          crate::cbordetver::cbor_det_array_iterator_next(
                                                                              &mut pi
                                                                          );
                                                                      validate_evercddl_label(c2)
                                                                  };
                                                              if ! cont
                                                              {
                                                                  (&mut pi)[0usize] = i11;
                                                                  (&mut pcont)[0usize] = false
                                                              }
                                                          };
                                                          true
                                                      }
                                                      else
                                                      { false };
                                                  if b_success
                                                  {
                                                      let
                                                      i·:
                                                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                      =
                                                          (&pi)[0usize];
                                                      crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                          i·
                                                      )
                                                  }
                                                  else
                                                  { false }
                                              }
                                              else
                                              { false }
                                          }
                                          else
                                          { false }
                                      };
                                  let test3: bool =
                                      if test2
                                      { true }
                                      else
                                      {
                                          let k2: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(chd);
                                          let mt1: u8 = crate::cbordetver::cbor_det_major_type(k2);
                                          let is_uint1: bool =
                                              mt1 == crate::cbordetveraux::cbor_major_type_uint64;
                                          let testk2: bool =
                                              if is_uint1
                                              {
                                                  let v2: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(k2);
                                                  let i: u64 =
                                                      match v2
                                                      {
                                                          crate::cbordetver::cbor_det_view::Int64
                                                          { value: res, .. }
                                                          => res,
                                                          _ => panic!("Incomplete pattern matching")
                                                      };
                                                  i == 3u64
                                              }
                                              else
                                              { false };
                                          if testk2
                                          {
                                              let v2: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(chd);
                                              let test3: bool = validate_tstr(v2);
                                              if test3 { true } else { validate_int(v2) }
                                          }
                                          else
                                          { false }
                                      };
                                  let test4: bool =
                                      if test3
                                      { true }
                                      else
                                      {
                                          let k2: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(chd);
                                          let mt1: u8 = crate::cbordetver::cbor_det_major_type(k2);
                                          let is_uint1: bool =
                                              mt1 == crate::cbordetveraux::cbor_major_type_uint64;
                                          let testk2: bool =
                                              if is_uint1
                                              {
                                                  let v2: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(k2);
                                                  let i: u64 =
                                                      match v2
                                                      {
                                                          crate::cbordetver::cbor_det_view::Int64
                                                          { value: res, .. }
                                                          => res,
                                                          _ => panic!("Incomplete pattern matching")
                                                      };
                                                  i == 4u64
                                              }
                                              else
                                              { false };
                                          if testk2
                                          {
                                              let v2: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(chd);
                                              validate_bstr(v2)
                                          }
                                          else
                                          { false }
                                      };
                                  let test5: bool =
                                      if test4
                                      { true }
                                      else
                                      {
                                          let k2: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(chd);
                                          let mt1: u8 = crate::cbordetver::cbor_det_major_type(k2);
                                          let is_uint1: bool =
                                              mt1 == crate::cbordetveraux::cbor_major_type_uint64;
                                          let testk2: bool =
                                              if is_uint1
                                              {
                                                  let v2: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(k2);
                                                  let i: u64 =
                                                      match v2
                                                      {
                                                          crate::cbordetver::cbor_det_view::Int64
                                                          { value: res, .. }
                                                          => res,
                                                          _ => panic!("Incomplete pattern matching")
                                                      };
                                                  i == 5u64
                                              }
                                              else
                                              { false };
                                          if testk2
                                          {
                                              let discarded: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(chd);
                                              crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(
                                                  discarded
                                              );
                                              true
                                          }
                                          else
                                          { false }
                                      };
                                  let test6: bool =
                                      if test5
                                      { true }
                                      else
                                      {
                                          let k2: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(chd);
                                          let mt1: u8 = crate::cbordetver::cbor_det_major_type(k2);
                                          let is_uint1: bool =
                                              mt1 == crate::cbordetveraux::cbor_major_type_uint64;
                                          let testk2: bool =
                                              if is_uint1
                                              {
                                                  let v2: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(k2);
                                                  let i: u64 =
                                                      match v2
                                                      {
                                                          crate::cbordetver::cbor_det_view::Int64
                                                          { value: res, .. }
                                                          => res,
                                                          _ => panic!("Incomplete pattern matching")
                                                      };
                                                  i == 6u64
                                              }
                                              else
                                              { false };
                                          if testk2
                                          {
                                              let discarded: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(chd);
                                              crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(
                                                  discarded
                                              );
                                              true
                                          }
                                          else
                                          { false }
                                      };
                                  ! test6
                              }
                              else
                              { false };
                          let test2: bool = ! test1;
                          if ! test2
                          {
                              let i: u64 = (&remaining)[0usize];
                              let i·: u64 = i.wrapping_sub(1u64);
                              (&mut remaining)[0usize] = i·
                          };
                          let
                          j1:
                          crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                          =
                              (&pj)[0usize];
                          let is_empty0: bool =
                              crate::cbordetver::cbor_det_map_iterator_is_empty(j1);
                          cond = ! is_empty0
                      };
                      crate::cbordetveraux::impl_map_group_result::MGOK
                  },
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        match res
        {
            crate::cbordetveraux::impl_map_group_result::MGOK =>
              {
                  let rem: u64 = (&remaining)[0usize];
                  rem == 0u64
              },
            crate::cbordetveraux::impl_map_group_result::MGFail => false,
            crate::cbordetveraux::impl_map_group_result::MGCutFail => false,
            _ => panic!("Precondition of the function most likely violated")
        }
    }
    else
    { false }
}

pub fn validate_empty_or_serialized_map(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    let test: bool = mt == crate::cbordetveraux::cbor_major_type_byte_string;
    let test1: bool =
        if test
        {
            let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let pl: &[u8] =
                match v
                {
                    crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let
            read:
            crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
            =
                crate::cbordetver::cbor_det_parse(pl);
            match read
            {
                crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
                => false,
                crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                { v: r }
                =>
                  {
                      let res: crate::cbordetveraux::cbor_raw = r.0;
                      let rem: &[u8] = r.1;
                      if rem.len() == 0usize { validate_header_map(res) } else { false }
                  },
                _ => panic!("Incomplete pattern matching")
            }
        }
        else
        { false };
    if test1
    { true }
    else
    {
        let mt1: u8 = crate::cbordetver::cbor_det_major_type(c);
        if mt1 == 2u8
        {
            let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let str: &[u8] =
                match v
                {
                    crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let len: usize = str.len();
            let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(0u64, len);
            let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 0u64);
            lo_ok && hi_ok
        }
        else
        { false }
    }
}

pub fn validate_nil(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    let test: bool = mt == crate::cbordetveraux::cbor_major_type_simple_value;
    if test
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let v1: u8 =
            match v
            {
                crate::cbordetver::cbor_det_view::SimpleValue { _0: res } => res,
                _ => panic!("Incomplete pattern matching")
            };
        v1 == 22u8
    }
    else
    { false }
}

pub fn validate_cose_sign1(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let ty: u8 = crate::cbordetver::cbor_det_major_type(c);
    if ty == crate::cbordetveraux::cbor_major_type_array
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
            match v
            {
                crate::cbordetver::cbor_det_view::Array { _0: a } =>
                  crate::cbordetver::cbor_det_array_iterator_start(a),
                _ => panic!("Incomplete pattern matching")
            };
        let mut pi: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
            [i; 1usize];
        let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
            (&pi)[0usize];
        let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
        let test1: bool =
            if is_done
            { false }
            else
            {
                let c1: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                validate_empty_or_serialized_map(c1)
            };
        let test11: bool =
            if test1
            {
                let i2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0usize];
                let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
                if is_done1
                { false }
                else
                {
                    let c1: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                    validate_header_map(c1)
                }
            }
            else
            { false };
        let b_success: bool =
            if test11
            {
                let i2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0usize];
                let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
                let test12: bool =
                    if is_done1
                    { false }
                    else
                    {
                        let c1: crate::cbordetveraux::cbor_raw =
                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                        let test: bool = validate_bstr(c1);
                        if test { true } else { validate_nil(c1) }
                    };
                if test12
                {
                    let i3: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                        (&pi)[0usize];
                    let is_done2: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i3);
                    if is_done2
                    { false }
                    else
                    {
                        let c1: crate::cbordetveraux::cbor_raw =
                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                        validate_bstr(c1)
                    }
                }
                else
                { false }
            }
            else
            { false };
        if b_success
        {
            let i·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pi)[0usize];
            crate::cbordetver::cbor_det_array_iterator_is_empty(i·)
        }
        else
        { false }
    }
    else
    { false }
}

pub fn validate_cose_sign1_tagged(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let k: u8 = crate::cbordetver::cbor_det_major_type(c);
    if k == crate::cbordetveraux::cbor_major_type_tagged
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let tag·: u64 =
            match v
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 18u64 == tag·
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let c·: crate::cbordetveraux::cbor_raw =
                match v1
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            validate_cose_sign1(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub fn evercddl_uint_right(x1: u64) -> u64 { x1 }

/**
Parser for evercddl_uint
*/
pub fn
parse_uint(c: crate::cbordetveraux::cbor_raw) ->
    u64
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    match v
    {
        crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn nint_right(x1: u64) -> u64 { x1 }

/**
Parser for nint
*/
pub fn
parse_nint(c: crate::cbordetveraux::cbor_raw) ->
    u64
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    match v
    {
        crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn evercddl_int_right(x2: evercddl_int_ugly) -> evercddl_int
{
    match x2
    {
        evercddl_int_ugly::Inl { v: x3 } => evercddl_int::Mkevercddl_int0 { _x0: x3 },
        evercddl_int_ugly::Inr { v: x4 } => evercddl_int::Mkevercddl_int1 { _x0: x4 },
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Parser for evercddl_int
*/
pub fn
parse_int(c: crate::cbordetveraux::cbor_raw) ->
    evercddl_int
{
    let test: bool = validate_uint(c);
    let res1: evercddl_int_ugly =
        if test
        {
            let res: u64 = parse_uint(c);
            evercddl_int_ugly::Inl { v: res }
        }
        else
        {
            let res: u64 = parse_nint(c);
            evercddl_int_ugly::Inr { v: res }
        };
    evercddl_int_right(res1)
}

pub fn tstr_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

/**
Parser for tstr
*/
pub fn
parse_tstr
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    match v
    {
        crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn aux_env34_validate_1(
    pi: &mut [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw]
) ->
    bool
{
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = pi[0usize];
    let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i);
    if is_done
    { false }
    else
    {
        let c: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_array_iterator_next(pi);
        validate_evercddl_label(c)
    }
}

pub fn evercddl_label_right <'a>(
    x2: either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t <'a>
) ->
    evercddl_label
    <'a>
{
    match x2
    {
        either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t::Inl { v: x3 } =>
          evercddl_label::Mkevercddl_label0 { _x0: x3 },
        either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t::Inr { v: x4 } =>
          evercddl_label::Mkevercddl_label1 { _x0: x4 },
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Parser for evercddl_label
*/
pub fn
parse_evercddl_label
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_label
    <'a>
{
    let test: bool = validate_int(c);
    let res1: either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t =
        if test
        {
            let res: evercddl_int = parse_int(c);
            either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t::Inl { v: res }
        }
        else
        {
            let res: &[u8] = parse_tstr(c);
            either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t::Inr { v: res }
        };
    evercddl_label_right(res1)
}

pub fn aux_env34_type_1_right <'a>(x1: evercddl_label <'a>) -> evercddl_label <'a> { x1 }

/**
Parser for aux_env34_type_1
*/
pub fn
aux_env34_parse_1
<'a>(c: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>) ->
    evercddl_label
    <'a>
{
    let mut pc: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c; 1usize];
    let x: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
    parse_evercddl_label(x)
}

pub fn bstr_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

/**
Parser for bstr
*/
pub fn
parse_bstr
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    match v
    {
        crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn everparsenomatch_right() { () }

/**
Parser for everparsenomatch
*/
pub fn
parse_everparsenomatch(c: crate::cbordetveraux::cbor_raw)
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    everparsenomatch_right()
}

pub fn any_right <'a>(x1: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x1 }

/**
Parser for any
*/
pub fn
parse_any
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ c }

pub fn values_right <'a>(x1: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x1 }

/**
Parser for values
*/
pub fn
parse_values
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ c }

pub fn header_map_right <'a>(
    x6:
    (((((option__FStar_Pervasives_either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t
    <'a>,
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
    <'a>),
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int
    <'a>),
    option__Pulse_Lib_Slice_slice·uint8_t
    <'a>),
    either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_FStar_Pervasives_either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···
    <'a>),
    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
    <'a>)
) ->
    header_map
    <'a>
{
    match x6
    {
        (((((x7,x8),x9),x10),x11),x12) =>
          header_map { intkey1: x7, intkey2: x8, intkey3: x9, intkey4: x10, _x0: x11, _x1: x12 }
    }
}

/**
Parser for header_map
*/
pub fn
parse_header_map
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    header_map
    <'a>
{
    let discarded: [u64; 1] = [0u64; 1usize];
    crate::lowstar::ignore::ignore::<[u64; 1]>(discarded);
    let mty: crate::cbordetver::cbor_det_int_kind = crate::cbordetver::cbor_det_int_kind::UInt64;
    let c1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty, 1u64);
    let x·: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let mg: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match x·
        {
            crate::cbordetver::cbor_det_view::Map { _0: m } =>
              crate::cbordetver::cbor_det_map_get(m, c1),
            _ => panic!("Incomplete pattern matching")
        };
    let test1: crate::cbordetveraux::impl_map_group_result =
        match mg
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
              crate::cbordetveraux::impl_map_group_result::MGFail,
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: cv } =>
              {
                  let test: bool = validate_int(cv);
                  let check_value: bool = if test { true } else { validate_tstr(cv) };
                  if check_value
                  { crate::cbordetveraux::impl_map_group_result::MGOK }
                  else
                  { crate::cbordetveraux::impl_map_group_result::MGFail }
              },
            _ => panic!("Incomplete pattern matching")
        };
    let
    w1: option__FStar_Pervasives_either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t
    =
        if
        match test1
        {
            crate::cbordetveraux::impl_map_group_result::MGOK => true,
            _tmp => false,
            _ => panic!("Incomplete pattern matching")
        }
        {
            let mty1: crate::cbordetver::cbor_det_int_kind =
                crate::cbordetver::cbor_det_int_kind::UInt64;
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty1, 1u64);
            let x·1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let ow: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match x·1
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m } =>
                      crate::cbordetver::cbor_det_map_get(m, c2),
                    _ => panic!("Incomplete pattern matching")
                };
            let w1: either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t =
                match ow
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      {
                          let test: bool = validate_int(w);
                          if test
                          {
                              let res: evercddl_int = parse_int(w);
                              either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t::Inl
                              { v: res }
                          }
                          else
                          {
                              let res: &[u8] = parse_tstr(w);
                              either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t::Inr
                              { v: res }
                          }
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            option__FStar_Pervasives_either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t::Some
            { v: w1 }
        }
        else
        {
            option__FStar_Pervasives_either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t::None
        };
    let discarded1: [u64; 1] = [0u64; 1usize];
    crate::lowstar::ignore::ignore::<[u64; 1]>(discarded1);
    let mty1: crate::cbordetver::cbor_det_int_kind = crate::cbordetver::cbor_det_int_kind::UInt64;
    let c2: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty1, 2u64);
    let x·1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let mg1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match x·1
        {
            crate::cbordetver::cbor_det_view::Map { _0: m } =>
              crate::cbordetver::cbor_det_map_get(m, c2),
            _ => panic!("Incomplete pattern matching")
        };
    let test11: crate::cbordetveraux::impl_map_group_result =
        match mg1
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
              crate::cbordetveraux::impl_map_group_result::MGFail,
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: cv } =>
              {
                  let ty: u8 = crate::cbordetver::cbor_det_major_type(cv);
                  let check_value: bool =
                      if ty == crate::cbordetveraux::cbor_major_type_array
                      {
                          let v: crate::cbordetver::cbor_det_view =
                              crate::cbordetver::cbor_det_destruct(cv);
                          let
                          i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                          =
                              match v
                              {
                                  crate::cbordetver::cbor_det_view::Array { _0: a } =>
                                    crate::cbordetver::cbor_det_array_iterator_start(a),
                                  _ => panic!("Incomplete pattern matching")
                              };
                          let
                          mut
                          pi:
                          [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
                          =
                              [i; 1usize];
                          let
                          i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                          =
                              (&pi)[0usize];
                          let is_done: bool =
                              crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
                          let test11: bool =
                              if is_done
                              { false }
                              else
                              {
                                  let c3: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                  validate_evercddl_label(c3)
                              };
                          let b_success: bool =
                              if test11
                              {
                                  let mut pcont: [bool; 1] = [true; 1usize];
                                  while
                                  (&pcont)[0usize]
                                  {
                                      let
                                      i11:
                                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                      =
                                          (&pi)[0usize];
                                      let
                                      i2:
                                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                      =
                                          (&pi)[0usize];
                                      let is_done1: bool =
                                          crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
                                      let cont: bool =
                                          if is_done1
                                          { false }
                                          else
                                          {
                                              let c3: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_array_iterator_next(
                                                      &mut pi
                                                  );
                                              validate_evercddl_label(c3)
                                          };
                                      if ! cont
                                      {
                                          (&mut pi)[0usize] = i11;
                                          (&mut pcont)[0usize] = false
                                      }
                                  };
                                  true
                              }
                              else
                              { false };
                          if b_success
                          {
                              let
                              i·:
                              crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                              =
                                  (&pi)[0usize];
                              crate::cbordetver::cbor_det_array_iterator_is_empty(i·)
                          }
                          else
                          { false }
                      }
                      else
                      { false };
                  if check_value
                  { crate::cbordetveraux::impl_map_group_result::MGOK }
                  else
                  { crate::cbordetveraux::impl_map_group_result::MGFail }
              },
            _ => panic!("Incomplete pattern matching")
        };
    let
    w2:
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
    =
        if
        match test11
        {
            crate::cbordetveraux::impl_map_group_result::MGOK => true,
            _tmp => false,
            _ => panic!("Incomplete pattern matching")
        }
        {
            let mty2: crate::cbordetver::cbor_det_int_kind =
                crate::cbordetver::cbor_det_int_kind::UInt64;
            let c3: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty2, 2u64);
            let x·2: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let ow: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match x·2
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m } =>
                      crate::cbordetver::cbor_det_map_get(m, c3),
                    _ => panic!("Incomplete pattern matching")
                };
            let
            w11:
            either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
            =
                match ow
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      {
                          let v: crate::cbordetver::cbor_det_view =
                              crate::cbordetver::cbor_det_destruct(w);
                          let
                          ar: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                          =
                              match v
                              {
                                  crate::cbordetver::cbor_det_view::Array { _0: a } =>
                                    crate::cbordetver::cbor_det_array_iterator_start(a),
                                  _ => panic!("Incomplete pattern matching")
                              };
                          let
                          i:
                          array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
                          =
                              array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
                              {
                                  cddl_array_iterator_contents: ar,
                                  cddl_array_iterator_impl_validate:
                                  aux_env34_validate_1
                                  as
                                  fn
                                  (&mut
                                  [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw])
                                  ->
                                  bool,
                                  cddl_array_iterator_impl_parse: aux_env34_parse_1
                              };
                          either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label::Inr
                          { v: i }
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label::Some
            { v: w11 }
        }
        else
        {
            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label::None
        };
    let
    w11:
    (option__FStar_Pervasives_either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t,
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label)
    =
        (w1,w2);
    let discarded2: [u64; 1] = [0u64; 1usize];
    crate::lowstar::ignore::ignore::<[u64; 1]>(discarded2);
    let mty2: crate::cbordetver::cbor_det_int_kind = crate::cbordetver::cbor_det_int_kind::UInt64;
    let c3: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty2, 3u64);
    let x·2: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let mg2: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match x·2
        {
            crate::cbordetver::cbor_det_view::Map { _0: m } =>
              crate::cbordetver::cbor_det_map_get(m, c3),
            _ => panic!("Incomplete pattern matching")
        };
    let test12: crate::cbordetveraux::impl_map_group_result =
        match mg2
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
              crate::cbordetveraux::impl_map_group_result::MGFail,
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: cv } =>
              {
                  let test: bool = validate_tstr(cv);
                  let check_value: bool = if test { true } else { validate_int(cv) };
                  if check_value
                  { crate::cbordetveraux::impl_map_group_result::MGOK }
                  else
                  { crate::cbordetveraux::impl_map_group_result::MGFail }
              },
            _ => panic!("Incomplete pattern matching")
        };
    let
    w21: option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int
    =
        if
        match test12
        {
            crate::cbordetveraux::impl_map_group_result::MGOK => true,
            _tmp => false,
            _ => panic!("Incomplete pattern matching")
        }
        {
            let mty3: crate::cbordetver::cbor_det_int_kind =
                crate::cbordetver::cbor_det_int_kind::UInt64;
            let c4: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty3, 3u64);
            let x·3: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let ow: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match x·3
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m } =>
                      crate::cbordetver::cbor_det_map_get(m, c4),
                    _ => panic!("Incomplete pattern matching")
                };
            let w12: either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int =
                match ow
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      {
                          let test: bool = validate_tstr(w);
                          if test
                          {
                              let res: &[u8] = parse_tstr(w);
                              either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Inl
                              { v: res }
                          }
                          else
                          {
                              let res: evercddl_int = parse_int(w);
                              either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Inr
                              { v: res }
                          }
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Some
            { v: w12 }
        }
        else
        {
            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::None
        };
    let
    w12:
    ((option__FStar_Pervasives_either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t,
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label),
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int)
    =
        (w11,w21);
    let discarded3: [u64; 1] = [0u64; 1usize];
    crate::lowstar::ignore::ignore::<[u64; 1]>(discarded3);
    let mty3: crate::cbordetver::cbor_det_int_kind = crate::cbordetver::cbor_det_int_kind::UInt64;
    let c4: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty3, 4u64);
    let x·3: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let mg3: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match x·3
        {
            crate::cbordetver::cbor_det_view::Map { _0: m } =>
              crate::cbordetver::cbor_det_map_get(m, c4),
            _ => panic!("Incomplete pattern matching")
        };
    let test13: crate::cbordetveraux::impl_map_group_result =
        match mg3
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
              crate::cbordetveraux::impl_map_group_result::MGFail,
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: cv } =>
              {
                  let check_value: bool = validate_bstr(cv);
                  if check_value
                  { crate::cbordetveraux::impl_map_group_result::MGOK }
                  else
                  { crate::cbordetveraux::impl_map_group_result::MGFail }
              },
            _ => panic!("Incomplete pattern matching")
        };
    let w22: option__Pulse_Lib_Slice_slice·uint8_t =
        if
        match test13
        {
            crate::cbordetveraux::impl_map_group_result::MGOK => true,
            _tmp => false,
            _ => panic!("Incomplete pattern matching")
        }
        {
            let mty4: crate::cbordetver::cbor_det_int_kind =
                crate::cbordetver::cbor_det_int_kind::UInt64;
            let c5: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty4, 4u64);
            let x·4: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let ow: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match x·4
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m } =>
                      crate::cbordetver::cbor_det_map_get(m, c5),
                    _ => panic!("Incomplete pattern matching")
                };
            let w13: &[u8] =
                match ow
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      parse_bstr(w),
                    _ => panic!("Incomplete pattern matching")
                };
            option__Pulse_Lib_Slice_slice·uint8_t::Some { v: w13 }
        }
        else
        { option__Pulse_Lib_Slice_slice·uint8_t::None };
    let
    w13:
    (((option__FStar_Pervasives_either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t,
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label),
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int),
    option__Pulse_Lib_Slice_slice·uint8_t)
    =
        (w12,w22);
    let mut dummy: [u64; 1] = [0u64; 1usize];
    let mty4: crate::cbordetver::cbor_det_int_kind = crate::cbordetver::cbor_det_int_kind::UInt64;
    let c5: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty4, 5u64);
    let x·4: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let mg4: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match x·4
        {
            crate::cbordetver::cbor_det_view::Map { _0: m } =>
              crate::cbordetver::cbor_det_map_get(m, c5),
            _ => panic!("Incomplete pattern matching")
        };
    let res1: crate::cbordetveraux::impl_map_group_result =
        match mg4
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
              crate::cbordetveraux::impl_map_group_result::MGFail,
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: cv } =>
              {
                  let check_value: bool = validate_bstr(cv);
                  if check_value
                  { crate::cbordetveraux::impl_map_group_result::MGOK }
                  else
                  { crate::cbordetveraux::impl_map_group_result::MGFail }
              },
            _ => panic!("Incomplete pattern matching")
        };
    let test14: crate::cbordetveraux::impl_map_group_result =
        match res1
        {
            crate::cbordetveraux::impl_map_group_result::MGOK =>
              {
                  let i0: u64 = (&dummy)[0usize];
                  let mty5: crate::cbordetver::cbor_det_int_kind =
                      crate::cbordetver::cbor_det_int_kind::UInt64;
                  let c6: crate::cbordetveraux::cbor_raw =
                      crate::cbordetver::cbor_det_mk_int64(mty5, 6u64);
                  let x·5: crate::cbordetver::cbor_det_view =
                      crate::cbordetver::cbor_det_destruct(c);
                  let mg5: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                      match x·5
                      {
                          crate::cbordetver::cbor_det_view::Map { _0: m } =>
                            crate::cbordetver::cbor_det_map_get(m, c6),
                          _ => panic!("Incomplete pattern matching")
                      };
                  let res11: crate::cbordetveraux::impl_map_group_result =
                      match mg5
                      {
                          crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                            crate::cbordetveraux::impl_map_group_result::MGFail,
                          crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: cv } =>
                            {
                                let check_value: bool = validate_everparsenomatch(cv);
                                if check_value
                                { crate::cbordetveraux::impl_map_group_result::MGOK }
                                else
                                { crate::cbordetveraux::impl_map_group_result::MGCutFail }
                            },
                          _ => panic!("Incomplete pattern matching")
                      };
                  match res11
                  {
                      crate::cbordetveraux::impl_map_group_result::MGOK =>
                        crate::cbordetveraux::impl_map_group_result::MGOK,
                      crate::cbordetveraux::impl_map_group_result::MGFail =>
                        {
                            (&mut dummy)[0usize] = i0;
                            crate::cbordetveraux::impl_map_group_result::MGOK
                        },
                      crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                        crate::cbordetveraux::impl_map_group_result::MGCutFail,
                      _ => panic!("Precondition of the function most likely violated")
                  }
              },
            crate::cbordetveraux::impl_map_group_result::MGFail =>
              crate::cbordetveraux::impl_map_group_result::MGFail,
            crate::cbordetveraux::impl_map_group_result::MGCutFail =>
              crate::cbordetveraux::impl_map_group_result::MGCutFail,
            _ => panic!("Precondition of the function most likely violated")
        };
    let
    w23:
    either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_FStar_Pervasives_either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···
    =
        if
        match test14
        {
            crate::cbordetveraux::impl_map_group_result::MGOK => true,
            _tmp => false,
            _ => panic!("Incomplete pattern matching")
        }
        {
            let mty5: crate::cbordetver::cbor_det_int_kind =
                crate::cbordetver::cbor_det_int_kind::UInt64;
            let c6: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty5, 5u64);
            let x·5: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let ow: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match x·5
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m } =>
                      crate::cbordetver::cbor_det_map_get(m, c6),
                    _ => panic!("Incomplete pattern matching")
                };
            let w14: &[u8] =
                match ow
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      parse_bstr(w),
                    _ => panic!("Incomplete pattern matching")
                };
            let discarded4: [u64; 1] = [0u64; 1usize];
            crate::lowstar::ignore::ignore::<[u64; 1]>(discarded4);
            let mty6: crate::cbordetver::cbor_det_int_kind =
                crate::cbordetver::cbor_det_int_kind::UInt64;
            let c7: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty6, 6u64);
            let x·6: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let mg5: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match x·6
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m } =>
                      crate::cbordetver::cbor_det_map_get(m, c7),
                    _ => panic!("Incomplete pattern matching")
                };
            let test15: crate::cbordetveraux::impl_map_group_result =
                match mg5
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                      crate::cbordetveraux::impl_map_group_result::MGFail,
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: cv } =>
                      {
                          let check_value: bool = validate_everparsenomatch(cv);
                          if check_value
                          { crate::cbordetveraux::impl_map_group_result::MGOK }
                          else
                          { crate::cbordetveraux::impl_map_group_result::MGCutFail }
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            let
            w23:
            crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags
            =
                if
                match test15
                {
                    crate::cbordetveraux::impl_map_group_result::MGOK => true,
                    _tmp => false,
                    _ => panic!("Incomplete pattern matching")
                }
                {
                    let mty7: crate::cbordetver::cbor_det_int_kind =
                        crate::cbordetver::cbor_det_int_kind::UInt64;
                    let c8: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_mk_int64(mty7, 6u64);
                    let x·7: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(c);
                    let ow1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                        match x·7
                        {
                            crate::cbordetver::cbor_det_view::Map { _0: m } =>
                              crate::cbordetver::cbor_det_map_get(m, c8),
                            _ => panic!("Incomplete pattern matching")
                        };
                    match ow1
                    {
                        crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                          parse_everparsenomatch(w),
                        _ => panic!("Incomplete pattern matching")
                    };
                    crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags::Some
                }
                else
                {
                    crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags::None
                };
            let
            w15:
            (&[u8],
            crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags)
            =
                (w14,w23);
            either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_FStar_Pervasives_either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···::Inl
            { v: w15 }
        }
        else
        {
            let mut dummy1: [u64; 1] = [0u64; 1usize];
            let mty5: crate::cbordetver::cbor_det_int_kind =
                crate::cbordetver::cbor_det_int_kind::UInt64;
            let c6: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty5, 6u64);
            let x·5: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let mg5: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match x·5
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m } =>
                      crate::cbordetver::cbor_det_map_get(m, c6),
                    _ => panic!("Incomplete pattern matching")
                };
            let res11: crate::cbordetveraux::impl_map_group_result =
                match mg5
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                      crate::cbordetveraux::impl_map_group_result::MGFail,
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: cv } =>
                      {
                          let check_value: bool = validate_bstr(cv);
                          if check_value
                          { crate::cbordetveraux::impl_map_group_result::MGOK }
                          else
                          { crate::cbordetveraux::impl_map_group_result::MGFail }
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            let test15: crate::cbordetveraux::impl_map_group_result =
                match res11
                {
                    crate::cbordetveraux::impl_map_group_result::MGOK =>
                      {
                          let i0: u64 = (&dummy1)[0usize];
                          let mty6: crate::cbordetver::cbor_det_int_kind =
                              crate::cbordetver::cbor_det_int_kind::UInt64;
                          let c7: crate::cbordetveraux::cbor_raw =
                              crate::cbordetver::cbor_det_mk_int64(mty6, 5u64);
                          let x·6: crate::cbordetver::cbor_det_view =
                              crate::cbordetver::cbor_det_destruct(c);
                          let mg6: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                              match x·6
                              {
                                  crate::cbordetver::cbor_det_view::Map { _0: m } =>
                                    crate::cbordetver::cbor_det_map_get(m, c7),
                                  _ => panic!("Incomplete pattern matching")
                              };
                          let res12: crate::cbordetveraux::impl_map_group_result =
                              match mg6
                              {
                                  crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                                    crate::cbordetveraux::impl_map_group_result::MGFail,
                                  crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                  { v: cv }
                                  =>
                                    {
                                        let check_value: bool = validate_everparsenomatch(cv);
                                        if check_value
                                        { crate::cbordetveraux::impl_map_group_result::MGOK }
                                        else
                                        { crate::cbordetveraux::impl_map_group_result::MGCutFail }
                                    },
                                  _ => panic!("Incomplete pattern matching")
                              };
                          match res12
                          {
                              crate::cbordetveraux::impl_map_group_result::MGOK =>
                                crate::cbordetveraux::impl_map_group_result::MGOK,
                              crate::cbordetveraux::impl_map_group_result::MGFail =>
                                {
                                    (&mut dummy1)[0usize] = i0;
                                    crate::cbordetveraux::impl_map_group_result::MGOK
                                },
                              crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                                crate::cbordetveraux::impl_map_group_result::MGCutFail,
                              _ => panic!("Precondition of the function most likely violated")
                          }
                      },
                    crate::cbordetveraux::impl_map_group_result::MGFail =>
                      crate::cbordetveraux::impl_map_group_result::MGFail,
                    crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                      crate::cbordetveraux::impl_map_group_result::MGCutFail,
                    _ => panic!("Precondition of the function most likely violated")
                };
            let
            w23:
            either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···
            =
                if
                match test15
                {
                    crate::cbordetveraux::impl_map_group_result::MGOK => true,
                    _tmp => false,
                    _ => panic!("Incomplete pattern matching")
                }
                {
                    let mty6: crate::cbordetver::cbor_det_int_kind =
                        crate::cbordetver::cbor_det_int_kind::UInt64;
                    let c7: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_mk_int64(mty6, 6u64);
                    let x·6: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(c);
                    let ow: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                        match x·6
                        {
                            crate::cbordetver::cbor_det_view::Map { _0: m } =>
                              crate::cbordetver::cbor_det_map_get(m, c7),
                            _ => panic!("Incomplete pattern matching")
                        };
                    let w14: &[u8] =
                        match ow
                        {
                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                            { v: w }
                            => parse_bstr(w),
                            _ => panic!("Incomplete pattern matching")
                        };
                    let discarded4: [u64; 1] = [0u64; 1usize];
                    crate::lowstar::ignore::ignore::<[u64; 1]>(discarded4);
                    let mty7: crate::cbordetver::cbor_det_int_kind =
                        crate::cbordetver::cbor_det_int_kind::UInt64;
                    let c8: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_mk_int64(mty7, 5u64);
                    let x·7: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(c);
                    let mg6: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                        match x·7
                        {
                            crate::cbordetver::cbor_det_view::Map { _0: m } =>
                              crate::cbordetver::cbor_det_map_get(m, c8),
                            _ => panic!("Incomplete pattern matching")
                        };
                    let test16: crate::cbordetveraux::impl_map_group_result =
                        match mg6
                        {
                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                              crate::cbordetveraux::impl_map_group_result::MGFail,
                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                            { v: cv }
                            =>
                              {
                                  let check_value: bool = validate_everparsenomatch(cv);
                                  if check_value
                                  { crate::cbordetveraux::impl_map_group_result::MGOK }
                                  else
                                  { crate::cbordetveraux::impl_map_group_result::MGCutFail }
                              },
                            _ => panic!("Incomplete pattern matching")
                        };
                    let
                    w23:
                    crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags
                    =
                        if
                        match test16
                        {
                            crate::cbordetveraux::impl_map_group_result::MGOK => true,
                            _tmp => false,
                            _ => panic!("Incomplete pattern matching")
                        }
                        {
                            let mty8: crate::cbordetver::cbor_det_int_kind =
                                crate::cbordetver::cbor_det_int_kind::UInt64;
                            let c9: crate::cbordetveraux::cbor_raw =
                                crate::cbordetver::cbor_det_mk_int64(mty8, 5u64);
                            let x·8: crate::cbordetver::cbor_det_view =
                                crate::cbordetver::cbor_det_destruct(c);
                            let ow1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                                match x·8
                                {
                                    crate::cbordetver::cbor_det_view::Map { _0: m } =>
                                      crate::cbordetver::cbor_det_map_get(m, c9),
                                    _ => panic!("Incomplete pattern matching")
                                };
                            match ow1
                            {
                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                { v: w }
                                => parse_everparsenomatch(w),
                                _ => panic!("Incomplete pattern matching")
                            };
                            crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags::Some
                        }
                        else
                        {
                            crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags::None
                        };
                    let
                    w15:
                    (&[u8],
                    crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags)
                    =
                        (w14,w23);
                    either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···::Inl
                    { v: w15 }
                }
                else
                {
                    let discarded4: [u64; 1] = [0u64; 1usize];
                    crate::lowstar::ignore::ignore::<[u64; 1]>(discarded4);
                    let mty6: crate::cbordetver::cbor_det_int_kind =
                        crate::cbordetver::cbor_det_int_kind::UInt64;
                    let c7: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_mk_int64(mty6, 6u64);
                    let x·6: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(c);
                    let mg6: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                        match x·6
                        {
                            crate::cbordetver::cbor_det_view::Map { _0: m } =>
                              crate::cbordetver::cbor_det_map_get(m, c7),
                            _ => panic!("Incomplete pattern matching")
                        };
                    let test16: crate::cbordetveraux::impl_map_group_result =
                        match mg6
                        {
                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                              crate::cbordetveraux::impl_map_group_result::MGFail,
                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                            { v: cv }
                            =>
                              {
                                  let check_value: bool = validate_everparsenomatch(cv);
                                  if check_value
                                  { crate::cbordetveraux::impl_map_group_result::MGOK }
                                  else
                                  { crate::cbordetveraux::impl_map_group_result::MGCutFail }
                              },
                            _ => panic!("Incomplete pattern matching")
                        };
                    let
                    w14:
                    crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags
                    =
                        if
                        match test16
                        {
                            crate::cbordetveraux::impl_map_group_result::MGOK => true,
                            _tmp => false,
                            _ => panic!("Incomplete pattern matching")
                        }
                        {
                            let mty7: crate::cbordetver::cbor_det_int_kind =
                                crate::cbordetver::cbor_det_int_kind::UInt64;
                            let c8: crate::cbordetveraux::cbor_raw =
                                crate::cbordetver::cbor_det_mk_int64(mty7, 6u64);
                            let x·7: crate::cbordetver::cbor_det_view =
                                crate::cbordetver::cbor_det_destruct(c);
                            let ow: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                                match x·7
                                {
                                    crate::cbordetver::cbor_det_view::Map { _0: m } =>
                                      crate::cbordetver::cbor_det_map_get(m, c8),
                                    _ => panic!("Incomplete pattern matching")
                                };
                            match ow
                            {
                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                { v: w }
                                => parse_everparsenomatch(w),
                                _ => panic!("Incomplete pattern matching")
                            };
                            crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags::Some
                        }
                        else
                        {
                            crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags::None
                        };
                    let discarded5: [u64; 1] = [0u64; 1usize];
                    crate::lowstar::ignore::ignore::<[u64; 1]>(discarded5);
                    let mty7: crate::cbordetver::cbor_det_int_kind =
                        crate::cbordetver::cbor_det_int_kind::UInt64;
                    let c8: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_mk_int64(mty7, 5u64);
                    let x·7: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(c);
                    let mg7: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                        match x·7
                        {
                            crate::cbordetver::cbor_det_view::Map { _0: m } =>
                              crate::cbordetver::cbor_det_map_get(m, c8),
                            _ => panic!("Incomplete pattern matching")
                        };
                    let test17: crate::cbordetveraux::impl_map_group_result =
                        match mg7
                        {
                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                              crate::cbordetveraux::impl_map_group_result::MGFail,
                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                            { v: cv }
                            =>
                              {
                                  let check_value: bool = validate_everparsenomatch(cv);
                                  if check_value
                                  { crate::cbordetveraux::impl_map_group_result::MGOK }
                                  else
                                  { crate::cbordetveraux::impl_map_group_result::MGCutFail }
                              },
                            _ => panic!("Incomplete pattern matching")
                        };
                    let
                    w23:
                    crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags
                    =
                        if
                        match test17
                        {
                            crate::cbordetveraux::impl_map_group_result::MGOK => true,
                            _tmp => false,
                            _ => panic!("Incomplete pattern matching")
                        }
                        {
                            let mty8: crate::cbordetver::cbor_det_int_kind =
                                crate::cbordetver::cbor_det_int_kind::UInt64;
                            let c9: crate::cbordetveraux::cbor_raw =
                                crate::cbordetver::cbor_det_mk_int64(mty8, 5u64);
                            let x·8: crate::cbordetver::cbor_det_view =
                                crate::cbordetver::cbor_det_destruct(c);
                            let ow: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                                match x·8
                                {
                                    crate::cbordetver::cbor_det_view::Map { _0: m } =>
                                      crate::cbordetver::cbor_det_map_get(m, c9),
                                    _ => panic!("Incomplete pattern matching")
                                };
                            match ow
                            {
                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                { v: w }
                                => parse_everparsenomatch(w),
                                _ => panic!("Incomplete pattern matching")
                            };
                            crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags::Some
                        }
                        else
                        {
                            crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags::None
                        };
                    let
                    w24:
                    (crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags,
                    crate::cbordetveraux::option__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags)
                    =
                        (w14,w23);
                    either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···::Inr
                    { v: w24 }
                };
            either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_FStar_Pervasives_either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···::Inr
            { v: w23 }
        };
    let
    w14:
    ((((option__FStar_Pervasives_either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t,
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label),
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int),
    option__Pulse_Lib_Slice_slice·uint8_t),
    either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_FStar_Pervasives_either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···)
    =
        (w13,w23);
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
        match v
        {
            crate::cbordetver::cbor_det_view::Map { _0: a } =>
              crate::cbordetver::cbor_det_map_iterator_start(a),
            _ => panic!("Incomplete pattern matching")
        };
    let
    rres:
    map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
    =
        map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
        {
            cddl_map_iterator_contents: i,
            cddl_map_iterator_impl_validate1:
            validate_evercddl_label as fn (crate::cbordetveraux::cbor_raw) -> bool,
            cddl_map_iterator_impl_parse1: parse_evercddl_label,
            cddl_map_iterator_impl_validate_ex:
            aux_env34_map_constraint_2 as fn (crate::cbordetveraux::cbor_map_entry) -> bool,
            cddl_map_iterator_impl_validate2:
            validate_values as fn (crate::cbordetveraux::cbor_raw) -> bool,
            cddl_map_iterator_impl_parse2: parse_values
        };
    let
    w24:
    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
    =
        either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw::Inr
        { v: rres };
    let
    res11:
    (((((option__FStar_Pervasives_either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t,
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_evercddl_label_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label),
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int),
    option__Pulse_Lib_Slice_slice·uint8_t),
    either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_FStar_Pervasives_either__·Pulse_Lib_Slice_slice·uint8_t···FStar_Pervasives_Native_option__···_·FStar_Pervasives_Native_option__·····FStar_Pervasives_Native_option__···),
    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw)
    =
        (w14,w24);
    header_map_right(res11)
}

pub fn empty_or_serialized_map_right <'a>(x2: empty_or_serialized_map_ugly <'a>) ->
    empty_or_serialized_map
    <'a>
{
    match x2
    {
        empty_or_serialized_map_ugly::Inl { v: x3 } =>
          empty_or_serialized_map::Mkempty_or_serialized_map0 { _x0: x3 },
        empty_or_serialized_map_ugly::Inr { v: x4 } =>
          empty_or_serialized_map::Mkempty_or_serialized_map1 { _x0: x4 },
        _ => panic!("Incomplete pattern matching")
    }
}

fn fst__CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice·uint8_t <'a>(
    x: (crate::cbordetveraux::cbor_raw <'a>, &'a [u8])
) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{
    let _1: crate::cbordetveraux::cbor_raw = x.0;
    let __2: &[u8] = x.1;
    _1
}

/**
Parser for empty_or_serialized_map
*/
pub fn
parse_empty_or_serialized_map
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    empty_or_serialized_map
    <'a>
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    let test: bool = mt == crate::cbordetveraux::cbor_major_type_byte_string;
    let test1: bool =
        if test
        {
            let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let pl: &[u8] =
                match v
                {
                    crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let
            read:
            crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
            =
                crate::cbordetver::cbor_det_parse(pl);
            match read
            {
                crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
                => false,
                crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                { v: r }
                =>
                  {
                      let res: crate::cbordetveraux::cbor_raw = r.0;
                      let rem: &[u8] = r.1;
                      if rem.len() == 0usize { validate_header_map(res) } else { false }
                  },
                _ => panic!("Incomplete pattern matching")
            }
        }
        else
        { false };
    let res1: empty_or_serialized_map_ugly =
        if test1
        {
            let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let cs: &[u8] =
                match v
                {
                    crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let
            cp:
            crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
            =
                crate::cbordetver::cbor_det_parse(cs);
            let res: header_map =
                match cp
                {
                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                    { v: cp_ }
                    =>
                      {
                          let cp1: crate::cbordetveraux::cbor_raw =
                              fst__CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice·uint8_t(cp_);
                          parse_header_map(cp1)
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            empty_or_serialized_map_ugly::Inl { v: res }
        }
        else
        {
            let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let res: &[u8] =
                match v
                {
                    crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            empty_or_serialized_map_ugly::Inr { v: res }
        };
    empty_or_serialized_map_right(res1)
}

pub fn nil_right() { () }

/**
Parser for nil
*/
pub fn
parse_nil(c: crate::cbordetveraux::cbor_raw)
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    nil_right()
}

pub fn cose_sign1_right <'a>(
    x4:
    ((empty_or_serialized_map <'a>, header_map <'a>),
    (either__Pulse_Lib_Slice_slice·uint8_t_·· <'a>, &'a [u8]))
) ->
    cose_sign1
    <'a>
{
    match x4
    {
        ((x5,x6),(x7,x8)) =>
          cose_sign1 { protected: x5, unprotected: x6, payload: x7, signature: x8 }
    }
}

/**
Parser for cose_sign1
*/
pub fn
parse_cose_sign1
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    cose_sign1
    <'a>
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let ar: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        match v
        {
            crate::cbordetver::cbor_det_view::Array { _0: a } =>
              crate::cbordetver::cbor_det_array_iterator_start(a),
            _ => panic!("Incomplete pattern matching")
        };
    let rlen0: u64 = crate::cbordetver::cbor_det_array_iterator_length(ar);
    let mut pc: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [ar; 1usize];
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0usize];
    let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i);
    let test1: bool =
        if is_done
        { false }
        else
        {
            let c1: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
            validate_empty_or_serialized_map(c1)
        };
    let discarded: bool =
        if test1
        {
            let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc)[0usize];
            let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
            if is_done1
            { false }
            else
            {
                let c1: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
                validate_header_map(c1)
            }
        }
        else
        { false };
    crate::lowstar::ignore::ignore::<bool>(discarded);
    let c1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0usize];
    let rlen1: u64 = crate::cbordetver::cbor_det_array_iterator_length(c1);
    let c0·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(ar, rlen0.wrapping_sub(rlen1));
    let rlen01: u64 = crate::cbordetver::cbor_det_array_iterator_length(c0·);
    let mut pc1: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·; 1usize];
    let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc1)[0usize];
    let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
    let discarded1: bool =
        if is_done1
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc1);
            validate_empty_or_serialized_map(c2)
        };
    crate::lowstar::ignore::ignore::<bool>(discarded1);
    let c11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        (&pc1)[0usize];
    let rlen11: u64 = crate::cbordetver::cbor_det_array_iterator_length(c11);
    let c0·1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c0·, rlen01.wrapping_sub(rlen11));
    let mut pc2: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·1; 1usize];
    let x: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc2);
    let w1: empty_or_serialized_map = parse_empty_or_serialized_map(x);
    let mut pc3: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c11; 1usize];
    let x1: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc3);
    let w2: header_map = parse_header_map(x1);
    let w11: (empty_or_serialized_map, header_map) = (w1,w2);
    let rlen02: u64 = crate::cbordetver::cbor_det_array_iterator_length(c1);
    let mut pc4: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c1; 1usize];
    let i2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc4)[0usize];
    let is_done2: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
    let discarded2: bool =
        if is_done2
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc4);
            let test: bool = validate_bstr(c2);
            if test { true } else { validate_nil(c2) }
        };
    crate::lowstar::ignore::ignore::<bool>(discarded2);
    let c12: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        (&pc4)[0usize];
    let rlen12: u64 = crate::cbordetver::cbor_det_array_iterator_length(c12);
    let c0·2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c1, rlen02.wrapping_sub(rlen12));
    let mut pc5: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·2; 1usize];
    let x2: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc5);
    let test: bool = validate_bstr(x2);
    let w12: either__Pulse_Lib_Slice_slice·uint8_t_·· =
        if test
        {
            let res: &[u8] = parse_bstr(x2);
            either__Pulse_Lib_Slice_slice·uint8_t_··::Inl { v: res }
        }
        else
        {
            parse_nil(x2);
            either__Pulse_Lib_Slice_slice·uint8_t_··::Inr
        };
    let mut pc6: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c12; 1usize];
    let x3: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc6);
    let w21: &[u8] = parse_bstr(x3);
    let w22: (either__Pulse_Lib_Slice_slice·uint8_t_··, &[u8]) = (w12,w21);
    let
    res1:
    ((empty_or_serialized_map, header_map), (either__Pulse_Lib_Slice_slice·uint8_t_··, &[u8]))
    =
        (w11,w22);
    cose_sign1_right(res1)
}

pub fn cose_sign1_tagged_right <'a>(x1: cose_sign1 <'a>) -> cose_sign1 <'a> { x1 }

/**
Parser for cose_sign1_tagged
*/
pub fn
parse_cose_sign1_tagged
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    cose_sign1
    <'a>
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let cpl: crate::cbordetveraux::cbor_raw =
        match v
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    parse_cose_sign1(cpl)
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_cose_sign1···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (cose_sign1 <'a>, &'a [u8]) }
}

pub fn validate_and_parse_cose_sign1_tagged <'a>(s: &'a [u8]) ->
    option__·COSE_Format_cose_sign1···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·COSE_Format_cose_sign1···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_cose_sign1_tagged(rl);
              if test
              {
                  let x: cose_sign1 = parse_cose_sign1_tagged(rl);
                  option__·COSE_Format_cose_sign1···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_cose_sign1···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_bool(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    let test: bool = mt == crate::cbordetveraux::cbor_major_type_simple_value;
    let test1: bool =
        if test
        {
            let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let v1: u8 =
                match v
                {
                    crate::cbordetver::cbor_det_view::SimpleValue { _0: res } => res,
                    _ => panic!("Incomplete pattern matching")
                };
            v1 == crate::cbordetveraux::cddl_simple_value_false
        }
        else
        { false };
    if test1
    { true }
    else
    {
        let mt1: u8 = crate::cbordetver::cbor_det_major_type(c);
        let test2: bool = mt1 == crate::cbordetveraux::cbor_major_type_simple_value;
        if test2
        {
            let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let v1: u8 =
                match v
                {
                    crate::cbordetver::cbor_det_view::SimpleValue { _0: res } => res,
                    _ => panic!("Incomplete pattern matching")
                };
            v1 == crate::cbordetveraux::cddl_simple_value_true
        }
        else
        { false }
    }
}

pub type evercddl_bool_ugly = bool;

pub type evercddl_bool = bool;

pub fn evercddl_bool_right(x1: bool) -> bool { x1 }

pub fn evercddl_bool_left(x4: bool) -> bool { x4 }

/**
Parser for evercddl_bool
*/
pub fn
parse_bool(c: crate::cbordetveraux::cbor_raw) ->
    bool
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let w: u8 =
        match v
        {
            crate::cbordetver::cbor_det_view::SimpleValue { _0: res } => res,
            _ => panic!("Incomplete pattern matching")
        };
    w == crate::cbordetveraux::simple_value_true
}

/**
Serializer for evercddl_bool
*/
pub fn
serialize_bool(c: bool, out: &mut [u8]) ->
    usize
{
    if c
    {
        if
        crate::cbordetveraux::simple_value_true
        <=
        crate::cbordetveraux::max_simple_value_additional_info
        ||
        crate::cbordetveraux::min_simple_value_long_argument
        <=
        crate::cbordetveraux::simple_value_true
        {
            let _letpattern: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                crate::cbordetver::cbor_det_mk_simple_value(crate::cbordetveraux::simple_value_true);
            let x: crate::cbordetveraux::cbor_raw =
                match _letpattern
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res } => res,
                    _ => panic!("Incomplete pattern matching")
                };
            let ser: crate::cbordetver::option__size_t =
                crate::cbordetver::cbor_det_serialize(x, out);
            match ser
            {
                crate::cbordetver::option__size_t::None => 0usize,
                crate::cbordetver::option__size_t::Some { v: sz } => sz,
                _ => panic!("Incomplete pattern matching")
            }
        }
        else
        { 0usize }
    }
    else if
    crate::cbordetveraux::simple_value_false
    <=
    crate::cbordetveraux::max_simple_value_additional_info
    ||
    crate::cbordetveraux::min_simple_value_long_argument
    <=
    crate::cbordetveraux::simple_value_false
    {
        let _letpattern: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
            crate::cbordetver::cbor_det_mk_simple_value(crate::cbordetveraux::simple_value_false);
        let x: crate::cbordetveraux::cbor_raw =
            match _letpattern
            {
                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res } => res,
                _ => panic!("Incomplete pattern matching")
            };
        let ser: crate::cbordetver::option__size_t = crate::cbordetver::cbor_det_serialize(x, out);
        match ser
        {
            crate::cbordetver::option__size_t::None => 0usize,
            crate::cbordetver::option__size_t::Some { v: sz } => sz,
            _ => panic!("Incomplete pattern matching")
        }
    }
    else
    { 0usize }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·bool···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (bool, &'a [u8]) }
}

pub fn validate_and_parse_bool <'a>(s: &'a [u8]) ->
    option__·bool···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·bool···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_bool(rl);
              if test
              {
                  let x: bool = parse_bool(rl);
                  option__·bool···Pulse_Lib_Slice_slice·uint8_t·::Some { v: (x,rem) }
              }
              else
              { option__·bool···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__······Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: ((), &'a [u8]) }
}

pub fn validate_and_parse_everparsenomatch <'a>(s: &'a [u8]) ->
    option__······Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__······Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_everparsenomatch(rl);
              if test
              {
                  parse_everparsenomatch(rl);
                  option__······Pulse_Lib_Slice_slice·uint8_t·::Some { v: ((),rem) }
              }
              else
              { option__······Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_and_parse_any <'a>(s: &'a [u8]) ->
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        =>
          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_any(rl);
              if test
              {
                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (rl,rem) }
              }
              else
              {
                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_undefined(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    let test: bool = mt == crate::cbordetveraux::cbor_major_type_simple_value;
    if test
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let v1: u8 =
            match v
            {
                crate::cbordetver::cbor_det_view::SimpleValue { _0: res } => res,
                _ => panic!("Incomplete pattern matching")
            };
        v1 == 23u8
    }
    else
    { false }
}

pub fn undefined_right() { () }

/**
Parser for undefined
*/
pub fn
parse_undefined(c: crate::cbordetveraux::cbor_raw)
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    undefined_right()
}

/**
Serializer for undefined
*/
pub fn
serialize_undefined(out: &mut [u8]) ->
    usize
{
    let _letpattern: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_mk_simple_value(23u8);
    let c1: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res } => res,
            _ => panic!("Incomplete pattern matching")
        };
    let res: crate::cbordetver::option__size_t = crate::cbordetver::cbor_det_serialize(c1, out);
    match res
    {
        crate::cbordetver::option__size_t::None => 0usize,
        crate::cbordetver::option__size_t::Some { v: r } => r,
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_and_parse_undefined <'a>(s: &'a [u8]) ->
    option__······Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__······Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_undefined(rl);
              if test
              {
                  parse_undefined(rl);
                  option__······Pulse_Lib_Slice_slice·uint8_t·::Some { v: ((),rem) }
              }
              else
              { option__······Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_and_parse_nil <'a>(s: &'a [u8]) ->
    option__······Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__······Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_nil(rl);
              if test
              {
                  parse_nil(rl);
                  option__······Pulse_Lib_Slice_slice·uint8_t·::Some { v: ((),rem) }
              }
              else
              { option__······Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_null(c: crate::cbordetveraux::cbor_raw) -> bool { validate_nil(c) }

pub fn evercddl_null_right() { () }

pub fn evercddl_null_left() { () }

/**
Parser for evercddl_null
*/
pub fn
parse_null(c: crate::cbordetveraux::cbor_raw)
{
    parse_nil(c);
    evercddl_null_right()
}

/**
Serializer for evercddl_null
*/
pub fn
serialize_null(out: &mut [u8]) ->
    usize
{ serialize_nil(out) }

pub fn validate_and_parse_null <'a>(s: &'a [u8]) ->
    option__······Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__······Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_null(rl);
              if test
              {
                  parse_null(rl);
                  option__······Pulse_Lib_Slice_slice·uint8_t·::Some { v: ((),rem) }
              }
              else
              { option__······Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_true(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    let test: bool = mt == crate::cbordetveraux::cbor_major_type_simple_value;
    if test
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let v1: u8 =
            match v
            {
                crate::cbordetver::cbor_det_view::SimpleValue { _0: res } => res,
                _ => panic!("Incomplete pattern matching")
            };
        v1 == 21u8
    }
    else
    { false }
}

pub fn evercddl_true_right() { () }

/**
Parser for evercddl_true
*/
pub fn
parse_true(c: crate::cbordetveraux::cbor_raw)
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    evercddl_true_right()
}

/**
Serializer for evercddl_true
*/
pub fn
serialize_true(out: &mut [u8]) ->
    usize
{
    let _letpattern: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_mk_simple_value(21u8);
    let c1: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res } => res,
            _ => panic!("Incomplete pattern matching")
        };
    let res: crate::cbordetver::option__size_t = crate::cbordetver::cbor_det_serialize(c1, out);
    match res
    {
        crate::cbordetver::option__size_t::None => 0usize,
        crate::cbordetver::option__size_t::Some { v: r } => r,
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_and_parse_true <'a>(s: &'a [u8]) ->
    option__······Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__······Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_true(rl);
              if test
              {
                  parse_true(rl);
                  option__······Pulse_Lib_Slice_slice·uint8_t·::Some { v: ((),rem) }
              }
              else
              { option__······Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_false(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    let test: bool = mt == crate::cbordetveraux::cbor_major_type_simple_value;
    if test
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let v1: u8 =
            match v
            {
                crate::cbordetver::cbor_det_view::SimpleValue { _0: res } => res,
                _ => panic!("Incomplete pattern matching")
            };
        v1 == 20u8
    }
    else
    { false }
}

pub fn evercddl_false_right() { () }

/**
Parser for evercddl_false
*/
pub fn
parse_false(c: crate::cbordetveraux::cbor_raw)
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    evercddl_false_right()
}

/**
Serializer for evercddl_false
*/
pub fn
serialize_false(out: &mut [u8]) ->
    usize
{
    let _letpattern: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_mk_simple_value(20u8);
    let c1: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res } => res,
            _ => panic!("Incomplete pattern matching")
        };
    let res: crate::cbordetver::option__size_t = crate::cbordetver::cbor_det_serialize(c1, out);
    match res
    {
        crate::cbordetver::option__size_t::None => 0usize,
        crate::cbordetver::option__size_t::Some { v: r } => r,
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_and_parse_false <'a>(s: &'a [u8]) ->
    option__······Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__······Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_false(rl);
              if test
              {
                  parse_false(rl);
                  option__······Pulse_Lib_Slice_slice·uint8_t·::Some { v: ((),rem) }
              }
              else
              { option__······Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_tstr <'a>(s: &'a [u8]) ->
    option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_tstr(rl);
              if test
              {
                  let x: &[u8] = parse_tstr(rl);
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_and_parse_bstr <'a>(s: &'a [u8]) ->
    option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_bstr(rl);
              if test
              {
                  let x: &[u8] = parse_bstr(rl);
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_bytes(c: crate::cbordetveraux::cbor_raw) -> bool { validate_bstr(c) }

pub fn bytes_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

pub fn bytes_left <'a>(x4: &'a [u8]) -> &'a [u8] { x4 }

/**
Parser for bytes
*/
pub fn
parse_bytes
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{ parse_bstr(c) }

/**
Serializer for bytes
*/
pub fn
serialize_bytes(c: &[u8], out: &mut [u8]) ->
    usize
{ serialize_bstr(c, out) }

pub fn validate_and_parse_bytes <'a>(s: &'a [u8]) ->
    option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_bytes(rl);
              if test
              {
                  let x: &[u8] = parse_bytes(rl);
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_text(c: crate::cbordetveraux::cbor_raw) -> bool { validate_tstr(c) }

pub fn text_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

pub fn text_left <'a>(x4: &'a [u8]) -> &'a [u8] { x4 }

/**
Parser for text
*/
pub fn
parse_text
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{ parse_tstr(c) }

/**
Serializer for text
*/
pub fn
serialize_text(c: &[u8], out: &mut [u8]) ->
    usize
{ serialize_tstr(c, out) }

pub fn validate_and_parse_text <'a>(s: &'a [u8]) ->
    option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_text(rl);
              if test
              {
                  let x: &[u8] = parse_text(rl);
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·uint64_t···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (u64, &'a [u8]) }
}

pub fn validate_and_parse_nint <'a>(s: &'a [u8]) ->
    option__·uint64_t···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·uint64_t···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_nint(rl);
              if test
              {
                  let x: u64 = parse_nint(rl);
                  option__·uint64_t···Pulse_Lib_Slice_slice·uint8_t·::Some { v: (x,rem) }
              }
              else
              { option__·uint64_t···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_and_parse_uint <'a>(s: &'a [u8]) ->
    option__·uint64_t···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·uint64_t···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_uint(rl);
              if test
              {
                  let x: u64 = parse_uint(rl);
                  option__·uint64_t···Pulse_Lib_Slice_slice·uint8_t·::Some { v: (x,rem) }
              }
              else
              { option__·uint64_t···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_int···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_int, &'a [u8]) }
}

pub fn validate_and_parse_int <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_int···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·COSE_Format_evercddl_int···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_int(rl);
              if test
              {
                  let x: evercddl_int = parse_int(rl);
                  option__·COSE_Format_evercddl_int···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_int···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_cborany(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let k: u8 = crate::cbordetver::cbor_det_major_type(c);
    if k == crate::cbordetveraux::cbor_major_type_tagged
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let tag·: u64 =
            match v
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 55799u64 == tag·
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let c·: crate::cbordetveraux::cbor_raw =
                match v1
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            validate_any(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub type cborany_ugly <'a> = crate::cbordetveraux::cbor_raw <'a>;

pub type cborany <'a> = crate::cbordetveraux::cbor_raw <'a>;

pub fn cborany_right <'a>(x1: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x1 }

pub fn cborany_left <'a>(x4: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x4 }

/**
Parser for cborany
*/
pub fn
parse_cborany
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    match v
    {
        crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Serializer for cborany
*/
pub fn
serialize_cborany(c: crate::cbordetveraux::cbor_raw, out: &mut [u8]) ->
    usize
{
    let c·: (u64, crate::cbordetveraux::cbor_raw) = (55799u64,c);
    let ctag: u64 = c·.0;
    let cpayload: crate::cbordetveraux::cbor_raw = c·.1;
    let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
    if tsz == 0usize
    { 0usize }
    else
    {
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
        let _tmp: &[u8] = _letpattern.0;
        let out2: &mut [u8] = _letpattern.1;
        let psz: usize = serialize_any(cpayload, out2);
        if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
    }
}

pub fn validate_and_parse_cborany <'a>(s: &'a [u8]) ->
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        =>
          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_cborany(rl);
              if test
              {
                  let x: crate::cbordetveraux::cbor_raw = parse_cborany(rl);
                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_mimemessage(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let k: u8 = crate::cbordetver::cbor_det_major_type(c);
    if k == crate::cbordetveraux::cbor_major_type_tagged
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let tag·: u64 =
            match v
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 36u64 == tag·
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let c·: crate::cbordetveraux::cbor_raw =
                match v1
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            validate_tstr(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub fn mimemessage_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

pub fn mimemessage_left <'a>(x4: &'a [u8]) -> &'a [u8] { x4 }

/**
Parser for mimemessage
*/
pub fn
parse_mimemessage
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let cpl: crate::cbordetveraux::cbor_raw =
        match v
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    parse_tstr(cpl)
}

/**
Serializer for mimemessage
*/
pub fn
serialize_mimemessage(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: (u64, &[u8]) = (36u64,c);
    let ctag: u64 = c·.0;
    let cpayload: &[u8] = c·.1;
    let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
    if tsz == 0usize
    { 0usize }
    else
    {
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
        let _tmp: &[u8] = _letpattern.0;
        let out2: &mut [u8] = _letpattern.1;
        let psz: usize = serialize_tstr(cpayload, out2);
        if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
    }
}

pub fn validate_and_parse_mimemessage <'a>(s: &'a [u8]) ->
    option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_mimemessage(rl);
              if test
              {
                  let x: &[u8] = parse_mimemessage(rl);
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_regexp(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let k: u8 = crate::cbordetver::cbor_det_major_type(c);
    if k == crate::cbordetveraux::cbor_major_type_tagged
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let tag·: u64 =
            match v
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 35u64 == tag·
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let c·: crate::cbordetveraux::cbor_raw =
                match v1
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            validate_tstr(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub fn regexp_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

pub fn regexp_left <'a>(x4: &'a [u8]) -> &'a [u8] { x4 }

/**
Parser for regexp
*/
pub fn
parse_regexp
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let cpl: crate::cbordetveraux::cbor_raw =
        match v
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    parse_tstr(cpl)
}

/**
Serializer for regexp
*/
pub fn
serialize_regexp(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: (u64, &[u8]) = (35u64,c);
    let ctag: u64 = c·.0;
    let cpayload: &[u8] = c·.1;
    let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
    if tsz == 0usize
    { 0usize }
    else
    {
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
        let _tmp: &[u8] = _letpattern.0;
        let out2: &mut [u8] = _letpattern.1;
        let psz: usize = serialize_tstr(cpayload, out2);
        if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
    }
}

pub fn validate_and_parse_regexp <'a>(s: &'a [u8]) ->
    option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_regexp(rl);
              if test
              {
                  let x: &[u8] = parse_regexp(rl);
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_b64legacy(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let k: u8 = crate::cbordetver::cbor_det_major_type(c);
    if k == crate::cbordetveraux::cbor_major_type_tagged
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let tag·: u64 =
            match v
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 34u64 == tag·
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let c·: crate::cbordetveraux::cbor_raw =
                match v1
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            validate_tstr(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub fn b64legacy_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

pub fn b64legacy_left <'a>(x4: &'a [u8]) -> &'a [u8] { x4 }

/**
Parser for b64legacy
*/
pub fn
parse_b64legacy
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let cpl: crate::cbordetveraux::cbor_raw =
        match v
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    parse_tstr(cpl)
}

/**
Serializer for b64legacy
*/
pub fn
serialize_b64legacy(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: (u64, &[u8]) = (34u64,c);
    let ctag: u64 = c·.0;
    let cpayload: &[u8] = c·.1;
    let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
    if tsz == 0usize
    { 0usize }
    else
    {
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
        let _tmp: &[u8] = _letpattern.0;
        let out2: &mut [u8] = _letpattern.1;
        let psz: usize = serialize_tstr(cpayload, out2);
        if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
    }
}

pub fn validate_and_parse_b64legacy <'a>(s: &'a [u8]) ->
    option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_b64legacy(rl);
              if test
              {
                  let x: &[u8] = parse_b64legacy(rl);
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_b64url(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let k: u8 = crate::cbordetver::cbor_det_major_type(c);
    if k == crate::cbordetveraux::cbor_major_type_tagged
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let tag·: u64 =
            match v
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 33u64 == tag·
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let c·: crate::cbordetveraux::cbor_raw =
                match v1
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            validate_tstr(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub fn b64url_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

pub fn b64url_left <'a>(x4: &'a [u8]) -> &'a [u8] { x4 }

/**
Parser for b64url
*/
pub fn
parse_b64url
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let cpl: crate::cbordetveraux::cbor_raw =
        match v
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    parse_tstr(cpl)
}

/**
Serializer for b64url
*/
pub fn
serialize_b64url(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: (u64, &[u8]) = (33u64,c);
    let ctag: u64 = c·.0;
    let cpayload: &[u8] = c·.1;
    let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
    if tsz == 0usize
    { 0usize }
    else
    {
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
        let _tmp: &[u8] = _letpattern.0;
        let out2: &mut [u8] = _letpattern.1;
        let psz: usize = serialize_tstr(cpayload, out2);
        if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
    }
}

pub fn validate_and_parse_b64url <'a>(s: &'a [u8]) ->
    option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_b64url(rl);
              if test
              {
                  let x: &[u8] = parse_b64url(rl);
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_uri(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let k: u8 = crate::cbordetver::cbor_det_major_type(c);
    if k == crate::cbordetveraux::cbor_major_type_tagged
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let tag·: u64 =
            match v
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 32u64 == tag·
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let c·: crate::cbordetveraux::cbor_raw =
                match v1
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            validate_tstr(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub fn uri_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

pub fn uri_left <'a>(x4: &'a [u8]) -> &'a [u8] { x4 }

/**
Parser for uri
*/
pub fn
parse_uri
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let cpl: crate::cbordetveraux::cbor_raw =
        match v
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    parse_tstr(cpl)
}

/**
Serializer for uri
*/
pub fn
serialize_uri(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: (u64, &[u8]) = (32u64,c);
    let ctag: u64 = c·.0;
    let cpayload: &[u8] = c·.1;
    let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
    if tsz == 0usize
    { 0usize }
    else
    {
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
        let _tmp: &[u8] = _letpattern.0;
        let out2: &mut [u8] = _letpattern.1;
        let psz: usize = serialize_tstr(cpayload, out2);
        if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
    }
}

pub fn validate_and_parse_uri <'a>(s: &'a [u8]) ->
    option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_uri(rl);
              if test
              {
                  let x: &[u8] = parse_uri(rl);
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_encodedcbor(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let k: u8 = crate::cbordetver::cbor_det_major_type(c);
    if k == crate::cbordetveraux::cbor_major_type_tagged
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let tag·: u64 =
            match v
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 24u64 == tag·
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let c·: crate::cbordetveraux::cbor_raw =
                match v1
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            validate_bstr(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub fn encodedcbor_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

pub fn encodedcbor_left <'a>(x4: &'a [u8]) -> &'a [u8] { x4 }

/**
Parser for encodedcbor
*/
pub fn
parse_encodedcbor
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let cpl: crate::cbordetveraux::cbor_raw =
        match v
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    parse_bstr(cpl)
}

/**
Serializer for encodedcbor
*/
pub fn
serialize_encodedcbor(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: (u64, &[u8]) = (24u64,c);
    let ctag: u64 = c·.0;
    let cpayload: &[u8] = c·.1;
    let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
    if tsz == 0usize
    { 0usize }
    else
    {
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
        let _tmp: &[u8] = _letpattern.0;
        let out2: &mut [u8] = _letpattern.1;
        let psz: usize = serialize_bstr(cpayload, out2);
        if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
    }
}

pub fn validate_and_parse_encodedcbor <'a>(s: &'a [u8]) ->
    option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_encodedcbor(rl);
              if test
              {
                  let x: &[u8] = parse_encodedcbor(rl);
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_eb16(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let k: u8 = crate::cbordetver::cbor_det_major_type(c);
    if k == crate::cbordetveraux::cbor_major_type_tagged
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let tag·: u64 =
            match v
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 23u64 == tag·
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let c·: crate::cbordetveraux::cbor_raw =
                match v1
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            validate_any(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub type eb16_ugly <'a> = crate::cbordetveraux::cbor_raw <'a>;

pub type eb16 <'a> = crate::cbordetveraux::cbor_raw <'a>;

pub fn eb16_right <'a>(x1: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x1 }

pub fn eb16_left <'a>(x4: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x4 }

/**
Parser for eb16
*/
pub fn
parse_eb16
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    match v
    {
        crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Serializer for eb16
*/
pub fn
serialize_eb16(c: crate::cbordetveraux::cbor_raw, out: &mut [u8]) ->
    usize
{
    let c·: (u64, crate::cbordetveraux::cbor_raw) = (23u64,c);
    let ctag: u64 = c·.0;
    let cpayload: crate::cbordetveraux::cbor_raw = c·.1;
    let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
    if tsz == 0usize
    { 0usize }
    else
    {
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
        let _tmp: &[u8] = _letpattern.0;
        let out2: &mut [u8] = _letpattern.1;
        let psz: usize = serialize_any(cpayload, out2);
        if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
    }
}

pub fn validate_and_parse_eb16 <'a>(s: &'a [u8]) ->
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        =>
          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_eb16(rl);
              if test
              {
                  let x: crate::cbordetveraux::cbor_raw = parse_eb16(rl);
                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_eb64legacy(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let k: u8 = crate::cbordetver::cbor_det_major_type(c);
    if k == crate::cbordetveraux::cbor_major_type_tagged
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let tag·: u64 =
            match v
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 22u64 == tag·
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let c·: crate::cbordetveraux::cbor_raw =
                match v1
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            validate_any(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub type eb64legacy_ugly <'a> = crate::cbordetveraux::cbor_raw <'a>;

pub type eb64legacy <'a> = crate::cbordetveraux::cbor_raw <'a>;

pub fn eb64legacy_right <'a>(x1: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x1 }

pub fn eb64legacy_left <'a>(x4: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x4 }

/**
Parser for eb64legacy
*/
pub fn
parse_eb64legacy
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    match v
    {
        crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Serializer for eb64legacy
*/
pub fn
serialize_eb64legacy(c: crate::cbordetveraux::cbor_raw, out: &mut [u8]) ->
    usize
{
    let c·: (u64, crate::cbordetveraux::cbor_raw) = (22u64,c);
    let ctag: u64 = c·.0;
    let cpayload: crate::cbordetveraux::cbor_raw = c·.1;
    let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
    if tsz == 0usize
    { 0usize }
    else
    {
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
        let _tmp: &[u8] = _letpattern.0;
        let out2: &mut [u8] = _letpattern.1;
        let psz: usize = serialize_any(cpayload, out2);
        if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
    }
}

pub fn validate_and_parse_eb64legacy <'a>(s: &'a [u8]) ->
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        =>
          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_eb64legacy(rl);
              if test
              {
                  let x: crate::cbordetveraux::cbor_raw = parse_eb64legacy(rl);
                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_eb64url(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let k: u8 = crate::cbordetver::cbor_det_major_type(c);
    if k == crate::cbordetveraux::cbor_major_type_tagged
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let tag·: u64 =
            match v
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 21u64 == tag·
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let c·: crate::cbordetveraux::cbor_raw =
                match v1
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            validate_any(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub type eb64url_ugly <'a> = crate::cbordetveraux::cbor_raw <'a>;

pub type eb64url <'a> = crate::cbordetveraux::cbor_raw <'a>;

pub fn eb64url_right <'a>(x1: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x1 }

pub fn eb64url_left <'a>(x4: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x4 }

/**
Parser for eb64url
*/
pub fn
parse_eb64url
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    match v
    {
        crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Serializer for eb64url
*/
pub fn
serialize_eb64url(c: crate::cbordetveraux::cbor_raw, out: &mut [u8]) ->
    usize
{
    let c·: (u64, crate::cbordetveraux::cbor_raw) = (21u64,c);
    let ctag: u64 = c·.0;
    let cpayload: crate::cbordetveraux::cbor_raw = c·.1;
    let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
    if tsz == 0usize
    { 0usize }
    else
    {
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
        let _tmp: &[u8] = _letpattern.0;
        let out2: &mut [u8] = _letpattern.1;
        let psz: usize = serialize_any(cpayload, out2);
        if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
    }
}

pub fn validate_and_parse_eb64url <'a>(s: &'a [u8]) ->
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        =>
          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_eb64url(rl);
              if test
              {
                  let x: crate::cbordetveraux::cbor_raw = parse_eb64url(rl);
                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_number(c: crate::cbordetveraux::cbor_raw) -> bool { validate_int(c) }

pub type number_ugly = evercddl_int;

pub type number = evercddl_int;

pub fn number_right(x1: evercddl_int) -> evercddl_int { x1 }

pub fn number_left(x4: evercddl_int) -> evercddl_int { x4 }

/**
Parser for number
*/
pub fn
parse_number(c: crate::cbordetveraux::cbor_raw) ->
    evercddl_int
{ parse_int(c) }

/**
Serializer for number
*/
pub fn
serialize_number(c: evercddl_int, out: &mut [u8]) ->
    usize
{ serialize_int(c, out) }

pub fn validate_and_parse_number <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_int···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·COSE_Format_evercddl_int···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_number(rl);
              if test
              {
                  let x: evercddl_int = parse_number(rl);
                  option__·COSE_Format_evercddl_int···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_int···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_tdate(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let k: u8 = crate::cbordetver::cbor_det_major_type(c);
    if k == crate::cbordetveraux::cbor_major_type_tagged
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let tag·: u64 =
            match v
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 0u64 == tag·
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let c·: crate::cbordetveraux::cbor_raw =
                match v1
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            validate_tstr(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub fn tdate_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

pub fn tdate_left <'a>(x4: &'a [u8]) -> &'a [u8] { x4 }

/**
Parser for tdate
*/
pub fn
parse_tdate
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let cpl: crate::cbordetveraux::cbor_raw =
        match v
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    parse_tstr(cpl)
}

/**
Serializer for tdate
*/
pub fn
serialize_tdate(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: (u64, &[u8]) = (0u64,c);
    let ctag: u64 = c·.0;
    let cpayload: &[u8] = c·.1;
    let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
    if tsz == 0usize
    { 0usize }
    else
    {
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
        let _tmp: &[u8] = _letpattern.0;
        let out2: &mut [u8] = _letpattern.1;
        let psz: usize = serialize_tstr(cpayload, out2);
        if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
    }
}

pub fn validate_and_parse_tdate <'a>(s: &'a [u8]) ->
    option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_tdate(rl);
              if test
              {
                  let x: &[u8] = parse_tdate(rl);
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_and_parse_values <'a>(s: &'a [u8]) ->
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        =>
          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_values(rl);
              if test
              {
                  let x: crate::cbordetveraux::cbor_raw = parse_values(rl);
                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_label···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_label <'a>, &'a [u8]) }
}

pub fn validate_and_parse_evercddl_label <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_label···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·COSE_Format_evercddl_label···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_evercddl_label(rl);
              if test
              {
                  let x: evercddl_label = parse_evercddl_label(rl);
                  option__·COSE_Format_evercddl_label···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_label···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn aux_env29_validate_1(
    pi: &mut [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw]
) ->
    bool
{
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = pi[0usize];
    let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i);
    if is_done
    { false }
    else
    {
        let c: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_array_iterator_next(pi);
        let test: bool = validate_tstr(c);
        if test { true } else { validate_int(c) }
    }
}

pub type aux_env29_type_1_ugly <'a> =
either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int <'a>;

#[derive(PartialEq, Clone, Copy)]
enum aux_env29_type_1_tags
{
    Mkaux_env29_type_10,
    Mkaux_env29_type_11
}

#[derive(PartialEq, Clone, Copy)]
pub enum aux_env29_type_1 <'a>
{
    Mkaux_env29_type_10 { _x0: &'a [u8] },
    Mkaux_env29_type_11 { _x0: evercddl_int }
}

pub fn aux_env29_type_1_right <'a>(
    x2: either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int <'a>
) ->
    aux_env29_type_1
    <'a>
{
    match x2
    {
        either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Inl { v: x3 } =>
          aux_env29_type_1::Mkaux_env29_type_10 { _x0: x3 },
        either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Inr { v: x4 } =>
          aux_env29_type_1::Mkaux_env29_type_11 { _x0: x4 },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn aux_env29_type_1_left <'a>(x8: aux_env29_type_1 <'a>) ->
    either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int
    <'a>
{
    match x8
    {
        aux_env29_type_1::Mkaux_env29_type_10 { _x0: x10 } =>
          either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Inl { v: x10 },
        aux_env29_type_1::Mkaux_env29_type_11 { _x0: x12 } =>
          either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Inr { v: x12 },
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Parser for aux_env29_type_1
*/
pub fn
aux_env29_parse_1
<'a>(c: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>) ->
    aux_env29_type_1
    <'a>
{
    let mut pc: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c; 1usize];
    let x: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
    let test: bool = validate_tstr(x);
    let res1: either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int =
        if test
        {
            let res: &[u8] = parse_tstr(x);
            either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Inl { v: res }
        }
        else
        {
            let res: evercddl_int = parse_int(x);
            either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Inr { v: res }
        };
    aux_env29_type_1_right(res1)
}

/**
Serializer for aux_env29_type_1
*/
pub fn
aux_env29_serialize_1(
    c: aux_env29_type_1,
    out: &mut [u8],
    out_count: &mut [u64],
    out_size: &mut [usize]
) ->
    bool
{
    let count: u64 = out_count[0usize];
    if count < 18446744073709551615u64
    {
        let size: usize = out_size[0usize];
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
        let _out0: &[u8] = _letpattern.0;
        let out1: &mut [u8] = _letpattern.1;
        let size1: usize =
            match aux_env29_type_1_left(c)
            {
                either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Inl { v: c1 } =>
                  serialize_tstr(c1, out1),
                either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Inr { v: c2 } =>
                  serialize_int(c2, out1),
                _ => panic!("Incomplete pattern matching")
            };
        if size1 == 0usize
        { false }
        else
        {
            out_count[0usize] = count.wrapping_add(1u64);
            out_size[0usize] = size.wrapping_add(size1);
            true
        }
    }
    else
    { false }
}

pub fn aux_env29_map_constraint_2(x: crate::cbordetveraux::cbor_map_entry) -> bool
{
    let k: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
    let mt: u8 = crate::cbordetver::cbor_det_major_type(k);
    let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;
    let testk: bool =
        if is_uint
        {
            let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(k);
            let i: u64 =
                match v
                {
                    crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                    _ => panic!("Incomplete pattern matching")
                };
            i == 1u64
        }
        else
        { false };
    let test: bool =
        if testk
        {
            let discarded: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_map_entry_value(x);
            crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(discarded);
            true
        }
        else
        { false };
    let test1: bool =
        if test
        { true }
        else
        {
            let k1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
            let mt1: u8 = crate::cbordetver::cbor_det_major_type(k1);
            let is_uint1: bool = mt1 == crate::cbordetveraux::cbor_major_type_uint64;
            let testk1: bool =
                if is_uint1
                {
                    let v: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(k1);
                    let i: u64 =
                        match v
                        {
                            crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                            _ => panic!("Incomplete pattern matching")
                        };
                    i == 2u64
                }
                else
                { false };
            if testk1
            {
                let v: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_map_entry_value(x);
                validate_bstr(v)
            }
            else
            { false }
        };
    let test2: bool =
        if test1
        { true }
        else
        {
            let k1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
            let mt1: u8 = crate::cbordetver::cbor_det_major_type(k1);
            let is_uint1: bool = mt1 == crate::cbordetveraux::cbor_major_type_uint64;
            let testk1: bool =
                if is_uint1
                {
                    let v: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(k1);
                    let i: u64 =
                        match v
                        {
                            crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                            _ => panic!("Incomplete pattern matching")
                        };
                    i == 3u64
                }
                else
                { false };
            if testk1
            {
                let v: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_map_entry_value(x);
                let test2: bool = validate_tstr(v);
                if test2 { true } else { validate_int(v) }
            }
            else
            { false }
        };
    let test3: bool =
        if test2
        { true }
        else
        {
            let k1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
            let mt1: u8 = crate::cbordetver::cbor_det_major_type(k1);
            let is_uint1: bool = mt1 == crate::cbordetveraux::cbor_major_type_uint64;
            let testk1: bool =
                if is_uint1
                {
                    let v: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(k1);
                    let i: u64 =
                        match v
                        {
                            crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                            _ => panic!("Incomplete pattern matching")
                        };
                    i == 4u64
                }
                else
                { false };
            if testk1
            {
                let v: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_map_entry_value(x);
                let ty: u8 = crate::cbordetver::cbor_det_major_type(v);
                if ty == crate::cbordetveraux::cbor_major_type_array
                {
                    let v1: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(v);
                    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                        match v1
                        {
                            crate::cbordetver::cbor_det_view::Array { _0: a } =>
                              crate::cbordetver::cbor_det_array_iterator_start(a),
                            _ => panic!("Incomplete pattern matching")
                        };
                    let
                    mut
                    pi:
                    [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
                    =
                        [i; 1usize];
                    let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                        (&pi)[0usize];
                    let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
                    let test11: bool =
                        if is_done
                        { false }
                        else
                        {
                            let c: crate::cbordetveraux::cbor_raw =
                                crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                            let test3: bool = validate_tstr(c);
                            if test3 { true } else { validate_int(c) }
                        };
                    let b_success: bool =
                        if test11
                        {
                            let mut pcont: [bool; 1] = [true; 1usize];
                            while
                            (&pcont)[0usize]
                            {
                                let
                                i11:
                                crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                =
                                    (&pi)[0usize];
                                let
                                i2:
                                crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                =
                                    (&pi)[0usize];
                                let is_done1: bool =
                                    crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
                                let cont: bool =
                                    if is_done1
                                    { false }
                                    else
                                    {
                                        let c: crate::cbordetveraux::cbor_raw =
                                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                        let test3: bool = validate_tstr(c);
                                        if test3 { true } else { validate_int(c) }
                                    };
                                if ! cont
                                {
                                    (&mut pi)[0usize] = i11;
                                    (&mut pcont)[0usize] = false
                                }
                            };
                            true
                        }
                        else
                        { false };
                    if b_success
                    {
                        let
                        i·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                        =
                            (&pi)[0usize];
                        crate::cbordetver::cbor_det_array_iterator_is_empty(i·)
                    }
                    else
                    { false }
                }
                else
                { false }
            }
            else
            { false }
        };
    if test3
    { true }
    else
    {
        let k1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
        let mt1: u8 = crate::cbordetver::cbor_det_major_type(k1);
        let is_uint1: bool = mt1 == crate::cbordetveraux::cbor_major_type_uint64;
        let testk1: bool =
            if is_uint1
            {
                let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(k1);
                let i: u64 =
                    match v
                    {
                        crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                        _ => panic!("Incomplete pattern matching")
                    };
                i == 5u64
            }
            else
            { false };
        if testk1
        {
            let v: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_value(x);
            validate_bstr(v)
        }
        else
        { false }
    }
}

pub fn validate_cose_key_generic(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let ty: u8 = crate::cbordetver::cbor_det_major_type(c);
    if ty == crate::cbordetveraux::cbor_major_type_map
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let rem0: u64 =
            match v
            {
                crate::cbordetver::cbor_det_view::Map { _0: a } =>
                  crate::cbordetver::cbor_det_map_length(a),
                _ => panic!("Incomplete pattern matching")
            };
        let mut remaining: [u64; 1] = [rem0; 1usize];
        let mty: crate::cbordetver::cbor_det_int_kind =
            crate::cbordetver::cbor_det_int_kind::UInt64;
        let c1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty, 1u64);
        let x·: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let mg: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
            match x·
            {
                crate::cbordetver::cbor_det_view::Map { _0: m } =>
                  crate::cbordetver::cbor_det_map_get(m, c1),
                _ => panic!("Incomplete pattern matching")
            };
        let res1: crate::cbordetveraux::impl_map_group_result =
            match mg
            {
                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: cv } =>
                  {
                      let test: bool = validate_tstr(cv);
                      let check_value: bool = if test { true } else { validate_int(cv) };
                      if check_value
                      {
                          let i1: u64 = (&remaining)[0usize];
                          let i2: u64 = i1.wrapping_sub(1u64);
                          (&mut remaining)[0usize] = i2;
                          crate::cbordetveraux::impl_map_group_result::MGOK
                      }
                      else
                      { crate::cbordetveraux::impl_map_group_result::MGFail }
                  },
                _ => panic!("Incomplete pattern matching")
            };
        let res11: crate::cbordetveraux::impl_map_group_result =
            match res1
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  {
                      let i0: u64 = (&remaining)[0usize];
                      let mty1: crate::cbordetver::cbor_det_int_kind =
                          crate::cbordetver::cbor_det_int_kind::UInt64;
                      let c2: crate::cbordetveraux::cbor_raw =
                          crate::cbordetver::cbor_det_mk_int64(mty1, 2u64);
                      let x·1: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let mg1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                          match x·1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: m } =>
                                crate::cbordetver::cbor_det_map_get(m, c2),
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res11: crate::cbordetveraux::impl_map_group_result =
                          match mg1
                          {
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                                crate::cbordetveraux::impl_map_group_result::MGFail,
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                              { v: cv }
                              =>
                                {
                                    let check_value: bool = validate_bstr(cv);
                                    if check_value
                                    {
                                        let i1: u64 = (&remaining)[0usize];
                                        let i2: u64 = i1.wrapping_sub(1u64);
                                        (&mut remaining)[0usize] = i2;
                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                    }
                                    else
                                    { crate::cbordetveraux::impl_map_group_result::MGFail }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      match res11
                      {
                          crate::cbordetveraux::impl_map_group_result::MGOK =>
                            crate::cbordetveraux::impl_map_group_result::MGOK,
                          crate::cbordetveraux::impl_map_group_result::MGFail =>
                            {
                                (&mut remaining)[0usize] = i0;
                                crate::cbordetveraux::impl_map_group_result::MGOK
                            },
                          crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                            crate::cbordetveraux::impl_map_group_result::MGCutFail,
                          _ => panic!("Precondition of the function most likely violated")
                      }
                  },
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        let res12: crate::cbordetveraux::impl_map_group_result =
            match res11
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  {
                      let i0: u64 = (&remaining)[0usize];
                      let mty1: crate::cbordetver::cbor_det_int_kind =
                          crate::cbordetver::cbor_det_int_kind::UInt64;
                      let c2: crate::cbordetveraux::cbor_raw =
                          crate::cbordetver::cbor_det_mk_int64(mty1, 3u64);
                      let x·1: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let mg1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                          match x·1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: m } =>
                                crate::cbordetver::cbor_det_map_get(m, c2),
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res12: crate::cbordetveraux::impl_map_group_result =
                          match mg1
                          {
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                                crate::cbordetveraux::impl_map_group_result::MGFail,
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                              { v: cv }
                              =>
                                {
                                    let test: bool = validate_tstr(cv);
                                    let check_value: bool =
                                        if test { true } else { validate_int(cv) };
                                    if check_value
                                    {
                                        let i1: u64 = (&remaining)[0usize];
                                        let i2: u64 = i1.wrapping_sub(1u64);
                                        (&mut remaining)[0usize] = i2;
                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                    }
                                    else
                                    { crate::cbordetveraux::impl_map_group_result::MGFail }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      match res12
                      {
                          crate::cbordetveraux::impl_map_group_result::MGOK =>
                            crate::cbordetveraux::impl_map_group_result::MGOK,
                          crate::cbordetveraux::impl_map_group_result::MGFail =>
                            {
                                (&mut remaining)[0usize] = i0;
                                crate::cbordetveraux::impl_map_group_result::MGOK
                            },
                          crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                            crate::cbordetveraux::impl_map_group_result::MGCutFail,
                          _ => panic!("Precondition of the function most likely violated")
                      }
                  },
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        let res13: crate::cbordetveraux::impl_map_group_result =
            match res12
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  {
                      let i0: u64 = (&remaining)[0usize];
                      let mty1: crate::cbordetver::cbor_det_int_kind =
                          crate::cbordetver::cbor_det_int_kind::UInt64;
                      let c2: crate::cbordetveraux::cbor_raw =
                          crate::cbordetver::cbor_det_mk_int64(mty1, 4u64);
                      let x·1: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let mg1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                          match x·1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: m } =>
                                crate::cbordetver::cbor_det_map_get(m, c2),
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res13: crate::cbordetveraux::impl_map_group_result =
                          match mg1
                          {
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                                crate::cbordetveraux::impl_map_group_result::MGFail,
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                              { v: cv }
                              =>
                                {
                                    let ty1: u8 = crate::cbordetver::cbor_det_major_type(cv);
                                    let check_value: bool =
                                        if ty1 == crate::cbordetveraux::cbor_major_type_array
                                        {
                                            let v1: crate::cbordetver::cbor_det_view =
                                                crate::cbordetver::cbor_det_destruct(cv);
                                            let
                                            i:
                                            crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                            =
                                                match v1
                                                {
                                                    crate::cbordetver::cbor_det_view::Array
                                                    { _0: a }
                                                    =>
                                                      crate::cbordetver::cbor_det_array_iterator_start(
                                                          a
                                                      ),
                                                    _ => panic!("Incomplete pattern matching")
                                                };
                                            let
                                            mut
                                            pi:
                                            [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw;
                                            1]
                                            =
                                                [i; 1usize];
                                            let
                                            i1:
                                            crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                            =
                                                (&pi)[0usize];
                                            let is_done: bool =
                                                crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                    i1
                                                );
                                            let test1: bool =
                                                if is_done
                                                { false }
                                                else
                                                {
                                                    let c3: crate::cbordetveraux::cbor_raw =
                                                        crate::cbordetver::cbor_det_array_iterator_next(
                                                            &mut pi
                                                        );
                                                    let test: bool = validate_tstr(c3);
                                                    if test { true } else { validate_int(c3) }
                                                };
                                            let b_success: bool =
                                                if test1
                                                {
                                                    let mut pcont: [bool; 1] = [true; 1usize];
                                                    while
                                                    (&pcont)[0usize]
                                                    {
                                                        let
                                                        i11:
                                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                        =
                                                            (&pi)[0usize];
                                                        let
                                                        i2:
                                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                        =
                                                            (&pi)[0usize];
                                                        let is_done1: bool =
                                                            crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                                i2
                                                            );
                                                        let cont: bool =
                                                            if is_done1
                                                            { false }
                                                            else
                                                            {
                                                                let
                                                                c3: crate::cbordetveraux::cbor_raw
                                                                =
                                                                    crate::cbordetver::cbor_det_array_iterator_next(
                                                                        &mut pi
                                                                    );
                                                                let test: bool = validate_tstr(c3);
                                                                if test
                                                                { true }
                                                                else
                                                                { validate_int(c3) }
                                                            };
                                                        if ! cont
                                                        {
                                                            (&mut pi)[0usize] = i11;
                                                            (&mut pcont)[0usize] = false
                                                        }
                                                    };
                                                    true
                                                }
                                                else
                                                { false };
                                            if b_success
                                            {
                                                let
                                                i·:
                                                crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                =
                                                    (&pi)[0usize];
                                                crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                    i·
                                                )
                                            }
                                            else
                                            { false }
                                        }
                                        else
                                        { false };
                                    if check_value
                                    {
                                        let i1: u64 = (&remaining)[0usize];
                                        let i2: u64 = i1.wrapping_sub(1u64);
                                        (&mut remaining)[0usize] = i2;
                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                    }
                                    else
                                    { crate::cbordetveraux::impl_map_group_result::MGFail }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      match res13
                      {
                          crate::cbordetveraux::impl_map_group_result::MGOK =>
                            crate::cbordetveraux::impl_map_group_result::MGOK,
                          crate::cbordetveraux::impl_map_group_result::MGFail =>
                            {
                                (&mut remaining)[0usize] = i0;
                                crate::cbordetveraux::impl_map_group_result::MGOK
                            },
                          crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                            crate::cbordetveraux::impl_map_group_result::MGCutFail,
                          _ => panic!("Precondition of the function most likely violated")
                      }
                  },
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        let res14: crate::cbordetveraux::impl_map_group_result =
            match res13
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  {
                      let i0: u64 = (&remaining)[0usize];
                      let mty1: crate::cbordetver::cbor_det_int_kind =
                          crate::cbordetver::cbor_det_int_kind::UInt64;
                      let c2: crate::cbordetveraux::cbor_raw =
                          crate::cbordetver::cbor_det_mk_int64(mty1, 5u64);
                      let x·1: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let mg1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                          match x·1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: m } =>
                                crate::cbordetver::cbor_det_map_get(m, c2),
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res14: crate::cbordetveraux::impl_map_group_result =
                          match mg1
                          {
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                                crate::cbordetveraux::impl_map_group_result::MGFail,
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                              { v: cv }
                              =>
                                {
                                    let check_value: bool = validate_bstr(cv);
                                    if check_value
                                    {
                                        let i1: u64 = (&remaining)[0usize];
                                        let i2: u64 = i1.wrapping_sub(1u64);
                                        (&mut remaining)[0usize] = i2;
                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                    }
                                    else
                                    { crate::cbordetveraux::impl_map_group_result::MGFail }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      match res14
                      {
                          crate::cbordetveraux::impl_map_group_result::MGOK =>
                            crate::cbordetveraux::impl_map_group_result::MGOK,
                          crate::cbordetveraux::impl_map_group_result::MGFail =>
                            {
                                (&mut remaining)[0usize] = i0;
                                crate::cbordetveraux::impl_map_group_result::MGOK
                            },
                          crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                            crate::cbordetveraux::impl_map_group_result::MGCutFail,
                          _ => panic!("Precondition of the function most likely violated")
                      }
                  },
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        let res: crate::cbordetveraux::impl_map_group_result =
            match res14
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  {
                      let v1: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let
                      j0:
                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                      =
                          match v1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: a } =>
                                crate::cbordetver::cbor_det_map_iterator_start(a),
                              _ => panic!("Incomplete pattern matching")
                          };
                      let
                      mut
                      pj:
                      [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry;
                      1]
                      =
                          [j0; 1usize];
                      let
                      j: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                      =
                          (&pj)[0usize];
                      let is_empty: bool = crate::cbordetver::cbor_det_map_iterator_is_empty(j);
                      let mut cond: bool = ! is_empty;
                      while
                      cond
                      {
                          let chd: crate::cbordetveraux::cbor_map_entry =
                              crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
                          let k: crate::cbordetveraux::cbor_raw =
                              crate::cbordetver::cbor_det_map_entry_key(chd);
                          let testk: bool = validate_evercddl_label(k);
                          let test: bool =
                              if testk
                              {
                                  let v2: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_value(chd);
                                  validate_values(v2)
                              }
                              else
                              { false };
                          let test1: bool =
                              if test
                              {
                                  let k1: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_key(chd);
                                  let mt: u8 = crate::cbordetver::cbor_det_major_type(k1);
                                  let is_uint: bool =
                                      mt == crate::cbordetveraux::cbor_major_type_uint64;
                                  let testk1: bool =
                                      if is_uint
                                      {
                                          let v2: crate::cbordetver::cbor_det_view =
                                              crate::cbordetver::cbor_det_destruct(k1);
                                          let i: u64 =
                                              match v2
                                              {
                                                  crate::cbordetver::cbor_det_view::Int64
                                                  { value: res, .. }
                                                  => res,
                                                  _ => panic!("Incomplete pattern matching")
                                              };
                                          i == 1u64
                                      }
                                      else
                                      { false };
                                  let test1: bool =
                                      if testk1
                                      {
                                          let discarded: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_value(chd);
                                          crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(
                                              discarded
                                          );
                                          true
                                      }
                                      else
                                      { false };
                                  let test2: bool =
                                      if test1
                                      { true }
                                      else
                                      {
                                          let k2: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(chd);
                                          let mt1: u8 = crate::cbordetver::cbor_det_major_type(k2);
                                          let is_uint1: bool =
                                              mt1 == crate::cbordetveraux::cbor_major_type_uint64;
                                          let testk2: bool =
                                              if is_uint1
                                              {
                                                  let v2: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(k2);
                                                  let i: u64 =
                                                      match v2
                                                      {
                                                          crate::cbordetver::cbor_det_view::Int64
                                                          { value: res, .. }
                                                          => res,
                                                          _ => panic!("Incomplete pattern matching")
                                                      };
                                                  i == 2u64
                                              }
                                              else
                                              { false };
                                          if testk2
                                          {
                                              let v2: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(chd);
                                              validate_bstr(v2)
                                          }
                                          else
                                          { false }
                                      };
                                  let test3: bool =
                                      if test2
                                      { true }
                                      else
                                      {
                                          let k2: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(chd);
                                          let mt1: u8 = crate::cbordetver::cbor_det_major_type(k2);
                                          let is_uint1: bool =
                                              mt1 == crate::cbordetveraux::cbor_major_type_uint64;
                                          let testk2: bool =
                                              if is_uint1
                                              {
                                                  let v2: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(k2);
                                                  let i: u64 =
                                                      match v2
                                                      {
                                                          crate::cbordetver::cbor_det_view::Int64
                                                          { value: res, .. }
                                                          => res,
                                                          _ => panic!("Incomplete pattern matching")
                                                      };
                                                  i == 3u64
                                              }
                                              else
                                              { false };
                                          if testk2
                                          {
                                              let v2: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(chd);
                                              let test3: bool = validate_tstr(v2);
                                              if test3 { true } else { validate_int(v2) }
                                          }
                                          else
                                          { false }
                                      };
                                  let test4: bool =
                                      if test3
                                      { true }
                                      else
                                      {
                                          let k2: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(chd);
                                          let mt1: u8 = crate::cbordetver::cbor_det_major_type(k2);
                                          let is_uint1: bool =
                                              mt1 == crate::cbordetveraux::cbor_major_type_uint64;
                                          let testk2: bool =
                                              if is_uint1
                                              {
                                                  let v2: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(k2);
                                                  let i: u64 =
                                                      match v2
                                                      {
                                                          crate::cbordetver::cbor_det_view::Int64
                                                          { value: res, .. }
                                                          => res,
                                                          _ => panic!("Incomplete pattern matching")
                                                      };
                                                  i == 4u64
                                              }
                                              else
                                              { false };
                                          if testk2
                                          {
                                              let v2: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(chd);
                                              let ty1: u8 =
                                                  crate::cbordetver::cbor_det_major_type(v2);
                                              if ty1 == crate::cbordetveraux::cbor_major_type_array
                                              {
                                                  let v3: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(v2);
                                                  let
                                                  i:
                                                  crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                  =
                                                      match v3
                                                      {
                                                          crate::cbordetver::cbor_det_view::Array
                                                          { _0: a }
                                                          =>
                                                            crate::cbordetver::cbor_det_array_iterator_start(
                                                                a
                                                            ),
                                                          _ => panic!("Incomplete pattern matching")
                                                      };
                                                  let
                                                  mut
                                                  pi:
                                                  [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw;
                                                  1]
                                                  =
                                                      [i; 1usize];
                                                  let
                                                  i1:
                                                  crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                  =
                                                      (&pi)[0usize];
                                                  let is_done: bool =
                                                      crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                          i1
                                                      );
                                                  let test11: bool =
                                                      if is_done
                                                      { false }
                                                      else
                                                      {
                                                          let c2: crate::cbordetveraux::cbor_raw =
                                                              crate::cbordetver::cbor_det_array_iterator_next(
                                                                  &mut pi
                                                              );
                                                          let test4: bool = validate_tstr(c2);
                                                          if test4
                                                          { true }
                                                          else
                                                          { validate_int(c2) }
                                                      };
                                                  let b_success: bool =
                                                      if test11
                                                      {
                                                          let mut pcont: [bool; 1] = [true; 1usize];
                                                          while
                                                          (&pcont)[0usize]
                                                          {
                                                              let
                                                              i11:
                                                              crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                              =
                                                                  (&pi)[0usize];
                                                              let
                                                              i2:
                                                              crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                              =
                                                                  (&pi)[0usize];
                                                              let is_done1: bool =
                                                                  crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                                      i2
                                                                  );
                                                              let cont: bool =
                                                                  if is_done1
                                                                  { false }
                                                                  else
                                                                  {
                                                                      let
                                                                      c2:
                                                                      crate::cbordetveraux::cbor_raw
                                                                      =
                                                                          crate::cbordetver::cbor_det_array_iterator_next(
                                                                              &mut pi
                                                                          );
                                                                      let test4: bool =
                                                                          validate_tstr(c2);
                                                                      if test4
                                                                      { true }
                                                                      else
                                                                      { validate_int(c2) }
                                                                  };
                                                              if ! cont
                                                              {
                                                                  (&mut pi)[0usize] = i11;
                                                                  (&mut pcont)[0usize] = false
                                                              }
                                                          };
                                                          true
                                                      }
                                                      else
                                                      { false };
                                                  if b_success
                                                  {
                                                      let
                                                      i·:
                                                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                      =
                                                          (&pi)[0usize];
                                                      crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                          i·
                                                      )
                                                  }
                                                  else
                                                  { false }
                                              }
                                              else
                                              { false }
                                          }
                                          else
                                          { false }
                                      };
                                  let test5: bool =
                                      if test4
                                      { true }
                                      else
                                      {
                                          let k2: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(chd);
                                          let mt1: u8 = crate::cbordetver::cbor_det_major_type(k2);
                                          let is_uint1: bool =
                                              mt1 == crate::cbordetveraux::cbor_major_type_uint64;
                                          let testk2: bool =
                                              if is_uint1
                                              {
                                                  let v2: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(k2);
                                                  let i: u64 =
                                                      match v2
                                                      {
                                                          crate::cbordetver::cbor_det_view::Int64
                                                          { value: res, .. }
                                                          => res,
                                                          _ => panic!("Incomplete pattern matching")
                                                      };
                                                  i == 5u64
                                              }
                                              else
                                              { false };
                                          if testk2
                                          {
                                              let v2: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(chd);
                                              validate_bstr(v2)
                                          }
                                          else
                                          { false }
                                      };
                                  ! test5
                              }
                              else
                              { false };
                          let test2: bool = ! test1;
                          if ! test2
                          {
                              let i: u64 = (&remaining)[0usize];
                              let i·: u64 = i.wrapping_sub(1u64);
                              (&mut remaining)[0usize] = i·
                          };
                          let
                          j1:
                          crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                          =
                              (&pj)[0usize];
                          let is_empty0: bool =
                              crate::cbordetver::cbor_det_map_iterator_is_empty(j1);
                          cond = ! is_empty0
                      };
                      crate::cbordetveraux::impl_map_group_result::MGOK
                  },
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        match res
        {
            crate::cbordetveraux::impl_map_group_result::MGOK =>
              {
                  let rem: u64 = (&remaining)[0usize];
                  rem == 0u64
              },
            crate::cbordetveraux::impl_map_group_result::MGFail => false,
            crate::cbordetveraux::impl_map_group_result::MGCutFail => false,
            _ => panic!("Precondition of the function most likely violated")
        }
    }
    else
    { false }
}

#[derive(PartialEq, Clone, Copy)]
pub struct
array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
<'a>
{
    pub cddl_array_iterator_contents:
    crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>,
    pub cddl_array_iterator_impl_validate:
    fn (&mut [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw]) -> bool,
    pub cddl_array_iterator_impl_parse:
    for<'a1>
    fn
    (crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a1>)
    ->
    aux_env29_type_1
    <'a1>
}

#[derive(PartialEq, Clone, Copy)]
pub enum
either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
<'a>
{
    Inl { v: &'a [aux_env29_type_1 <'a>] },
    Inr
    {
        v:
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
        <'a>
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
<'a>
{
    None,
    Some
    {
        v:
        either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
        <'a>
    }
}

#[derive(PartialEq, Clone, Copy)]
pub struct cose_key_generic <'a>
{
    pub intkey1: either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int <'a>,
    pub intkey2: option__Pulse_Lib_Slice_slice·uint8_t <'a>,
    pub intkey3:
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int <'a>,
    pub intkey4:
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
    <'a>,
    pub intkey5: option__Pulse_Lib_Slice_slice·uint8_t <'a>,
    pub _x0:
    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
}

pub fn cose_key_generic_right <'a>(
    x6:
    (((((either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int
    <'a>,
    option__Pulse_Lib_Slice_slice·uint8_t
    <'a>),
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int
    <'a>),
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
    <'a>),
    option__Pulse_Lib_Slice_slice·uint8_t
    <'a>),
    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
    <'a>)
) ->
    cose_key_generic
    <'a>
{
    match x6
    {
        (((((x7,x8),x9),x10),x11),x12) =>
          cose_key_generic
          { intkey1: x7, intkey2: x8, intkey3: x9, intkey4: x10, intkey5: x11, _x0: x12 }
    }
}

pub fn cose_key_generic_left <'a>(x14: cose_key_generic <'a>) ->
    (((((either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int
    <'a>,
    option__Pulse_Lib_Slice_slice·uint8_t
    <'a>),
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int
    <'a>),
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
    <'a>),
    option__Pulse_Lib_Slice_slice·uint8_t
    <'a>),
    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
    <'a>)
{ (((((x14.intkey1,x14.intkey2),x14.intkey3),x14.intkey4),x14.intkey5),x14._x0) }

/**
Parser for cose_key_generic
*/
pub fn
parse_cose_key_generic
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    cose_key_generic
    <'a>
{
    let mty: crate::cbordetver::cbor_det_int_kind = crate::cbordetver::cbor_det_int_kind::UInt64;
    let c1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty, 1u64);
    let x·: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let ow: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match x·
        {
            crate::cbordetver::cbor_det_view::Map { _0: m } =>
              crate::cbordetver::cbor_det_map_get(m, c1),
            _ => panic!("Incomplete pattern matching")
        };
    let w1: either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int =
        match ow
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
              {
                  let test: bool = validate_tstr(w);
                  if test
                  {
                      let res: &[u8] = parse_tstr(w);
                      either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Inl
                      { v: res }
                  }
                  else
                  {
                      let res: evercddl_int = parse_int(w);
                      either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Inr
                      { v: res }
                  }
              },
            _ => panic!("Incomplete pattern matching")
        };
    let discarded: [u64; 1] = [0u64; 1usize];
    crate::lowstar::ignore::ignore::<[u64; 1]>(discarded);
    let mty1: crate::cbordetver::cbor_det_int_kind = crate::cbordetver::cbor_det_int_kind::UInt64;
    let c2: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty1, 2u64);
    let x·1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let mg: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match x·1
        {
            crate::cbordetver::cbor_det_view::Map { _0: m } =>
              crate::cbordetver::cbor_det_map_get(m, c2),
            _ => panic!("Incomplete pattern matching")
        };
    let test1: crate::cbordetveraux::impl_map_group_result =
        match mg
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
              crate::cbordetveraux::impl_map_group_result::MGFail,
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: cv } =>
              {
                  let check_value: bool = validate_bstr(cv);
                  if check_value
                  { crate::cbordetveraux::impl_map_group_result::MGOK }
                  else
                  { crate::cbordetveraux::impl_map_group_result::MGFail }
              },
            _ => panic!("Incomplete pattern matching")
        };
    let w2: option__Pulse_Lib_Slice_slice·uint8_t =
        if
        match test1
        {
            crate::cbordetveraux::impl_map_group_result::MGOK => true,
            _tmp => false,
            _ => panic!("Incomplete pattern matching")
        }
        {
            let mty2: crate::cbordetver::cbor_det_int_kind =
                crate::cbordetver::cbor_det_int_kind::UInt64;
            let c3: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty2, 2u64);
            let x·2: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let ow1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match x·2
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m } =>
                      crate::cbordetver::cbor_det_map_get(m, c3),
                    _ => panic!("Incomplete pattern matching")
                };
            let w11: &[u8] =
                match ow1
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      parse_bstr(w),
                    _ => panic!("Incomplete pattern matching")
                };
            option__Pulse_Lib_Slice_slice·uint8_t::Some { v: w11 }
        }
        else
        { option__Pulse_Lib_Slice_slice·uint8_t::None };
    let
    w11:
    (either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int,
    option__Pulse_Lib_Slice_slice·uint8_t)
    =
        (w1,w2);
    let discarded1: [u64; 1] = [0u64; 1usize];
    crate::lowstar::ignore::ignore::<[u64; 1]>(discarded1);
    let mty2: crate::cbordetver::cbor_det_int_kind = crate::cbordetver::cbor_det_int_kind::UInt64;
    let c3: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty2, 3u64);
    let x·2: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let mg1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match x·2
        {
            crate::cbordetver::cbor_det_view::Map { _0: m } =>
              crate::cbordetver::cbor_det_map_get(m, c3),
            _ => panic!("Incomplete pattern matching")
        };
    let test11: crate::cbordetveraux::impl_map_group_result =
        match mg1
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
              crate::cbordetveraux::impl_map_group_result::MGFail,
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: cv } =>
              {
                  let test: bool = validate_tstr(cv);
                  let check_value: bool = if test { true } else { validate_int(cv) };
                  if check_value
                  { crate::cbordetveraux::impl_map_group_result::MGOK }
                  else
                  { crate::cbordetveraux::impl_map_group_result::MGFail }
              },
            _ => panic!("Incomplete pattern matching")
        };
    let
    w21: option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int
    =
        if
        match test11
        {
            crate::cbordetveraux::impl_map_group_result::MGOK => true,
            _tmp => false,
            _ => panic!("Incomplete pattern matching")
        }
        {
            let mty3: crate::cbordetver::cbor_det_int_kind =
                crate::cbordetver::cbor_det_int_kind::UInt64;
            let c4: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty3, 3u64);
            let x·3: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let ow1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match x·3
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m } =>
                      crate::cbordetver::cbor_det_map_get(m, c4),
                    _ => panic!("Incomplete pattern matching")
                };
            let w12: either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int =
                match ow1
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      {
                          let test: bool = validate_tstr(w);
                          if test
                          {
                              let res: &[u8] = parse_tstr(w);
                              either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Inl
                              { v: res }
                          }
                          else
                          {
                              let res: evercddl_int = parse_int(w);
                              either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Inr
                              { v: res }
                          }
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Some
            { v: w12 }
        }
        else
        {
            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::None
        };
    let
    w12:
    ((either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int,
    option__Pulse_Lib_Slice_slice·uint8_t),
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int)
    =
        (w11,w21);
    let discarded2: [u64; 1] = [0u64; 1usize];
    crate::lowstar::ignore::ignore::<[u64; 1]>(discarded2);
    let mty3: crate::cbordetver::cbor_det_int_kind = crate::cbordetver::cbor_det_int_kind::UInt64;
    let c4: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty3, 4u64);
    let x·3: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let mg2: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match x·3
        {
            crate::cbordetver::cbor_det_view::Map { _0: m } =>
              crate::cbordetver::cbor_det_map_get(m, c4),
            _ => panic!("Incomplete pattern matching")
        };
    let test12: crate::cbordetveraux::impl_map_group_result =
        match mg2
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
              crate::cbordetveraux::impl_map_group_result::MGFail,
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: cv } =>
              {
                  let ty: u8 = crate::cbordetver::cbor_det_major_type(cv);
                  let check_value: bool =
                      if ty == crate::cbordetveraux::cbor_major_type_array
                      {
                          let v: crate::cbordetver::cbor_det_view =
                              crate::cbordetver::cbor_det_destruct(cv);
                          let
                          i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                          =
                              match v
                              {
                                  crate::cbordetver::cbor_det_view::Array { _0: a } =>
                                    crate::cbordetver::cbor_det_array_iterator_start(a),
                                  _ => panic!("Incomplete pattern matching")
                              };
                          let
                          mut
                          pi:
                          [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
                          =
                              [i; 1usize];
                          let
                          i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                          =
                              (&pi)[0usize];
                          let is_done: bool =
                              crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
                          let test12: bool =
                              if is_done
                              { false }
                              else
                              {
                                  let c5: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                  let test: bool = validate_tstr(c5);
                                  if test { true } else { validate_int(c5) }
                              };
                          let b_success: bool =
                              if test12
                              {
                                  let mut pcont: [bool; 1] = [true; 1usize];
                                  while
                                  (&pcont)[0usize]
                                  {
                                      let
                                      i11:
                                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                      =
                                          (&pi)[0usize];
                                      let
                                      i2:
                                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                      =
                                          (&pi)[0usize];
                                      let is_done1: bool =
                                          crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
                                      let cont: bool =
                                          if is_done1
                                          { false }
                                          else
                                          {
                                              let c5: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_array_iterator_next(
                                                      &mut pi
                                                  );
                                              let test: bool = validate_tstr(c5);
                                              if test { true } else { validate_int(c5) }
                                          };
                                      if ! cont
                                      {
                                          (&mut pi)[0usize] = i11;
                                          (&mut pcont)[0usize] = false
                                      }
                                  };
                                  true
                              }
                              else
                              { false };
                          if b_success
                          {
                              let
                              i·:
                              crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                              =
                                  (&pi)[0usize];
                              crate::cbordetver::cbor_det_array_iterator_is_empty(i·)
                          }
                          else
                          { false }
                      }
                      else
                      { false };
                  if check_value
                  { crate::cbordetveraux::impl_map_group_result::MGOK }
                  else
                  { crate::cbordetveraux::impl_map_group_result::MGFail }
              },
            _ => panic!("Incomplete pattern matching")
        };
    let
    w22:
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
    =
        if
        match test12
        {
            crate::cbordetveraux::impl_map_group_result::MGOK => true,
            _tmp => false,
            _ => panic!("Incomplete pattern matching")
        }
        {
            let mty4: crate::cbordetver::cbor_det_int_kind =
                crate::cbordetver::cbor_det_int_kind::UInt64;
            let c5: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty4, 4u64);
            let x·4: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let ow1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match x·4
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m } =>
                      crate::cbordetver::cbor_det_map_get(m, c5),
                    _ => panic!("Incomplete pattern matching")
                };
            let
            w13:
            either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
            =
                match ow1
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      {
                          let v: crate::cbordetver::cbor_det_view =
                              crate::cbordetver::cbor_det_destruct(w);
                          let
                          ar: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                          =
                              match v
                              {
                                  crate::cbordetver::cbor_det_view::Array { _0: a } =>
                                    crate::cbordetver::cbor_det_array_iterator_start(a),
                                  _ => panic!("Incomplete pattern matching")
                              };
                          let
                          i:
                          array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
                          =
                              array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
                              {
                                  cddl_array_iterator_contents: ar,
                                  cddl_array_iterator_impl_validate:
                                  aux_env29_validate_1
                                  as
                                  fn
                                  (&mut
                                  [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw])
                                  ->
                                  bool,
                                  cddl_array_iterator_impl_parse: aux_env29_parse_1
                              };
                          either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1::Inr
                          { v: i }
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1::Some
            { v: w13 }
        }
        else
        {
            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1::None
        };
    let
    w13:
    (((either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int,
    option__Pulse_Lib_Slice_slice·uint8_t),
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int),
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1)
    =
        (w12,w22);
    let discarded3: [u64; 1] = [0u64; 1usize];
    crate::lowstar::ignore::ignore::<[u64; 1]>(discarded3);
    let mty4: crate::cbordetver::cbor_det_int_kind = crate::cbordetver::cbor_det_int_kind::UInt64;
    let c5: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty4, 5u64);
    let x·4: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let mg3: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match x·4
        {
            crate::cbordetver::cbor_det_view::Map { _0: m } =>
              crate::cbordetver::cbor_det_map_get(m, c5),
            _ => panic!("Incomplete pattern matching")
        };
    let test13: crate::cbordetveraux::impl_map_group_result =
        match mg3
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
              crate::cbordetveraux::impl_map_group_result::MGFail,
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: cv } =>
              {
                  let check_value: bool = validate_bstr(cv);
                  if check_value
                  { crate::cbordetveraux::impl_map_group_result::MGOK }
                  else
                  { crate::cbordetveraux::impl_map_group_result::MGFail }
              },
            _ => panic!("Incomplete pattern matching")
        };
    let w23: option__Pulse_Lib_Slice_slice·uint8_t =
        if
        match test13
        {
            crate::cbordetveraux::impl_map_group_result::MGOK => true,
            _tmp => false,
            _ => panic!("Incomplete pattern matching")
        }
        {
            let mty5: crate::cbordetver::cbor_det_int_kind =
                crate::cbordetver::cbor_det_int_kind::UInt64;
            let c6: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty5, 5u64);
            let x·5: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let ow1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match x·5
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m } =>
                      crate::cbordetver::cbor_det_map_get(m, c6),
                    _ => panic!("Incomplete pattern matching")
                };
            let w14: &[u8] =
                match ow1
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      parse_bstr(w),
                    _ => panic!("Incomplete pattern matching")
                };
            option__Pulse_Lib_Slice_slice·uint8_t::Some { v: w14 }
        }
        else
        { option__Pulse_Lib_Slice_slice·uint8_t::None };
    let
    w14:
    ((((either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int,
    option__Pulse_Lib_Slice_slice·uint8_t),
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int),
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1),
    option__Pulse_Lib_Slice_slice·uint8_t)
    =
        (w13,w23);
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
        match v
        {
            crate::cbordetver::cbor_det_view::Map { _0: a } =>
              crate::cbordetver::cbor_det_map_iterator_start(a),
            _ => panic!("Incomplete pattern matching")
        };
    let
    rres:
    map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
    =
        map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
        {
            cddl_map_iterator_contents: i,
            cddl_map_iterator_impl_validate1:
            validate_evercddl_label as fn (crate::cbordetveraux::cbor_raw) -> bool,
            cddl_map_iterator_impl_parse1: parse_evercddl_label,
            cddl_map_iterator_impl_validate_ex:
            aux_env29_map_constraint_2 as fn (crate::cbordetveraux::cbor_map_entry) -> bool,
            cddl_map_iterator_impl_validate2:
            validate_values as fn (crate::cbordetveraux::cbor_raw) -> bool,
            cddl_map_iterator_impl_parse2: parse_values
        };
    let
    w24:
    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
    =
        either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw::Inr
        { v: rres };
    let
    res1:
    (((((either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int,
    option__Pulse_Lib_Slice_slice·uint8_t),
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int),
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1),
    option__Pulse_Lib_Slice_slice·uint8_t),
    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw)
    =
        (w14,w24);
    cose_key_generic_right(res1)
}

/**
Serializer for cose_key_generic
*/
pub fn
serialize_cose_key_generic(c: cose_key_generic, out: &mut [u8]) ->
    usize
{
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let
    _letpattern:
    (((((either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int,
    option__Pulse_Lib_Slice_slice·uint8_t),
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int),
    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1),
    option__Pulse_Lib_Slice_slice·uint8_t),
    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw)
    =
        cose_key_generic_left(c);
    let res: bool =
        {
            let
            c1:
            ((((either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int,
            option__Pulse_Lib_Slice_slice·uint8_t),
            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int),
            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1),
            option__Pulse_Lib_Slice_slice·uint8_t)
            =
                _letpattern.0;
            let
            c2:
            either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
            =
                _letpattern.1;
            let res1: bool =
                {
                    let
                    c11:
                    (((either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int,
                    option__Pulse_Lib_Slice_slice·uint8_t),
                    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int),
                    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1)
                    =
                        c1.0;
                    let c21: option__Pulse_Lib_Slice_slice·uint8_t = c1.1;
                    let res1: bool =
                        {
                            let
                            c12:
                            ((either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int,
                            option__Pulse_Lib_Slice_slice·uint8_t),
                            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int)
                            =
                                c11.0;
                            let
                            c22:
                            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
                            =
                                c11.1;
                            let res1: bool =
                                {
                                    let
                                    c13:
                                    (either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int,
                                    option__Pulse_Lib_Slice_slice·uint8_t)
                                    =
                                        c12.0;
                                    let
                                    c23:
                                    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int
                                    =
                                        c12.1;
                                    let res1: bool =
                                        {
                                            let
                                            c14:
                                            either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int
                                            =
                                                c13.0;
                                            let c24: option__Pulse_Lib_Slice_slice·uint8_t = c13.1;
                                            let count: u64 = (&pcount)[0usize];
                                            let res1: bool =
                                                if count < 18446744073709551615u64
                                                {
                                                    let size0: usize = (&psize)[0usize];
                                                    let _letpattern1: (&mut [u8], &mut [u8]) =
                                                        out.split_at_mut(size0);
                                                    let _out0: &[u8] = _letpattern1.0;
                                                    let out1: &mut [u8] = _letpattern1.1;
                                                    let mty: crate::cbordetver::cbor_det_int_kind =
                                                        crate::cbordetver::cbor_det_int_kind::UInt64;
                                                    let c3: crate::cbordetveraux::cbor_raw =
                                                        crate::cbordetver::cbor_det_mk_int64(
                                                            mty,
                                                            1u64
                                                        );
                                                    let res: crate::cbordetver::option__size_t =
                                                        crate::cbordetver::cbor_det_serialize(
                                                            c3,
                                                            out1
                                                        );
                                                    let res1: usize =
                                                        match res
                                                        {
                                                            crate::cbordetver::option__size_t::None
                                                            => 0usize,
                                                            crate::cbordetver::option__size_t::Some
                                                            { v: r }
                                                            => r,
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        };
                                                    if res1 > 0usize
                                                    {
                                                        let size1: usize = size0.wrapping_add(res1);
                                                        let _letpattern2: (&mut [u8], &mut [u8]) =
                                                            out.split_at_mut(size1);
                                                        let _out01: &[u8] = _letpattern2.0;
                                                        let out2: &mut [u8] = _letpattern2.1;
                                                        let res2: usize =
                                                            match c14
                                                            {
                                                                either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Inl
                                                                { v: c15 }
                                                                => serialize_tstr(c15, out2),
                                                                either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Inr
                                                                { v: c25 }
                                                                => serialize_int(c25, out2),
                                                                _ =>
                                                                  panic!(
                                                                      "Incomplete pattern matching"
                                                                  )
                                                            };
                                                        if res2 > 0usize
                                                        {
                                                            let size2: usize =
                                                                size1.wrapping_add(res2);
                                                            let
                                                            _letpattern3: (&mut [u8], &mut [u8])
                                                            =
                                                                out.split_at_mut(size2);
                                                            let out012: &mut [u8] = _letpattern3.0;
                                                            let _out_rest: &[u8] = _letpattern3.1;
                                                            let res3: bool =
                                                                crate::cbordetver::cbor_det_serialize_map_insert(
                                                                    out012,
                                                                    size0,
                                                                    size1
                                                                );
                                                            if res3
                                                            {
                                                                (&mut psize)[0usize] = size2;
                                                                (&mut pcount)[0usize] =
                                                                    count.wrapping_add(1u64);
                                                                true
                                                            }
                                                            else
                                                            { false }
                                                        }
                                                        else
                                                        { false }
                                                    }
                                                    else
                                                    { false }
                                                }
                                                else
                                                { false };
                                            if res1
                                            {
                                                match c24
                                                {
                                                    option__Pulse_Lib_Slice_slice·uint8_t::Some
                                                    { v: c15 }
                                                    =>
                                                      {
                                                          let count1: u64 = (&pcount)[0usize];
                                                          if count1 < 18446744073709551615u64
                                                          {
                                                              let size0: usize = (&psize)[0usize];
                                                              let
                                                              _letpattern1: (&mut [u8], &mut [u8])
                                                              =
                                                                  out.split_at_mut(size0);
                                                              let _out0: &[u8] = _letpattern1.0;
                                                              let out1: &mut [u8] = _letpattern1.1;
                                                              let
                                                              mty:
                                                              crate::cbordetver::cbor_det_int_kind
                                                              =
                                                                  crate::cbordetver::cbor_det_int_kind::UInt64;
                                                              let
                                                              c3: crate::cbordetveraux::cbor_raw
                                                              =
                                                                  crate::cbordetver::cbor_det_mk_int64(
                                                                      mty,
                                                                      2u64
                                                                  );
                                                              let
                                                              res: crate::cbordetver::option__size_t
                                                              =
                                                                  crate::cbordetver::cbor_det_serialize(
                                                                      c3,
                                                                      out1
                                                                  );
                                                              let res11: usize =
                                                                  match res
                                                                  {
                                                                      crate::cbordetver::option__size_t::None
                                                                      => 0usize,
                                                                      crate::cbordetver::option__size_t::Some
                                                                      { v: r }
                                                                      => r,
                                                                      _ =>
                                                                        panic!(
                                                                            "Incomplete pattern matching"
                                                                        )
                                                                  };
                                                              if res11 > 0usize
                                                              {
                                                                  let size1: usize =
                                                                      size0.wrapping_add(res11);
                                                                  let
                                                                  _letpattern2:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size1);
                                                                  let _out01: &[u8] =
                                                                      _letpattern2.0;
                                                                  let out2: &mut [u8] =
                                                                      _letpattern2.1;
                                                                  let res2: usize =
                                                                      serialize_bstr(c15, out2);
                                                                  if res2 > 0usize
                                                                  {
                                                                      let size2: usize =
                                                                          size1.wrapping_add(res2);
                                                                      let
                                                                      _letpattern3:
                                                                      (&mut [u8], &mut [u8])
                                                                      =
                                                                          out.split_at_mut(size2);
                                                                      let out012: &mut [u8] =
                                                                          _letpattern3.0;
                                                                      let _out_rest: &[u8] =
                                                                          _letpattern3.1;
                                                                      let res3: bool =
                                                                          crate::cbordetver::cbor_det_serialize_map_insert(
                                                                              out012,
                                                                              size0,
                                                                              size1
                                                                          );
                                                                      if res3
                                                                      {
                                                                          (&mut psize)[0usize] =
                                                                              size2;
                                                                          (&mut pcount)[0usize] =
                                                                              count1.wrapping_add(
                                                                                  1u64
                                                                              );
                                                                          true
                                                                      }
                                                                      else
                                                                      { false }
                                                                  }
                                                                  else
                                                                  { false }
                                                              }
                                                              else
                                                              { false }
                                                          }
                                                          else
                                                          { false }
                                                      },
                                                    option__Pulse_Lib_Slice_slice·uint8_t::None =>
                                                      true,
                                                    _ => panic!("Incomplete pattern matching")
                                                }
                                            }
                                            else
                                            { false }
                                        };
                                    if res1
                                    {
                                        match c23
                                        {
                                            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Some
                                            { v: c14 }
                                            =>
                                              {
                                                  let count: u64 = (&pcount)[0usize];
                                                  if count < 18446744073709551615u64
                                                  {
                                                      let size0: usize = (&psize)[0usize];
                                                      let _letpattern1: (&mut [u8], &mut [u8]) =
                                                          out.split_at_mut(size0);
                                                      let _out0: &[u8] = _letpattern1.0;
                                                      let out1: &mut [u8] = _letpattern1.1;
                                                      let
                                                      mty: crate::cbordetver::cbor_det_int_kind
                                                      =
                                                          crate::cbordetver::cbor_det_int_kind::UInt64;
                                                      let c3: crate::cbordetveraux::cbor_raw =
                                                          crate::cbordetver::cbor_det_mk_int64(
                                                              mty,
                                                              3u64
                                                          );
                                                      let res: crate::cbordetver::option__size_t =
                                                          crate::cbordetver::cbor_det_serialize(
                                                              c3,
                                                              out1
                                                          );
                                                      let res11: usize =
                                                          match res
                                                          {
                                                              crate::cbordetver::option__size_t::None
                                                              => 0usize,
                                                              crate::cbordetver::option__size_t::Some
                                                              { v: r }
                                                              => r,
                                                              _ =>
                                                                panic!(
                                                                    "Incomplete pattern matching"
                                                                )
                                                          };
                                                      if res11 > 0usize
                                                      {
                                                          let size1: usize =
                                                              size0.wrapping_add(res11);
                                                          let _letpattern2: (&mut [u8], &mut [u8]) =
                                                              out.split_at_mut(size1);
                                                          let _out01: &[u8] = _letpattern2.0;
                                                          let out2: &mut [u8] = _letpattern2.1;
                                                          let res2: usize =
                                                              match c14
                                                              {
                                                                  either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Inl
                                                                  { v: c15 }
                                                                  => serialize_tstr(c15, out2),
                                                                  either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::Inr
                                                                  { v: c24 }
                                                                  => serialize_int(c24, out2),
                                                                  _ =>
                                                                    panic!(
                                                                        "Incomplete pattern matching"
                                                                    )
                                                              };
                                                          if res2 > 0usize
                                                          {
                                                              let size2: usize =
                                                                  size1.wrapping_add(res2);
                                                              let
                                                              _letpattern3: (&mut [u8], &mut [u8])
                                                              =
                                                                  out.split_at_mut(size2);
                                                              let out012: &mut [u8] =
                                                                  _letpattern3.0;
                                                              let _out_rest: &[u8] = _letpattern3.1;
                                                              let res3: bool =
                                                                  crate::cbordetver::cbor_det_serialize_map_insert(
                                                                      out012,
                                                                      size0,
                                                                      size1
                                                                  );
                                                              if res3
                                                              {
                                                                  (&mut psize)[0usize] = size2;
                                                                  (&mut pcount)[0usize] =
                                                                      count.wrapping_add(1u64);
                                                                  true
                                                              }
                                                              else
                                                              { false }
                                                          }
                                                          else
                                                          { false }
                                                      }
                                                      else
                                                      { false }
                                                  }
                                                  else
                                                  { false }
                                              },
                                            option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·uint8_t_COSE_Format_evercddl_int::None
                                            => true,
                                            _ => panic!("Incomplete pattern matching")
                                        }
                                    }
                                    else
                                    { false }
                                };
                            if res1
                            {
                                match c22
                                {
                                    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1::Some
                                    { v: c13 }
                                    =>
                                      {
                                          let count: u64 = (&pcount)[0usize];
                                          if count < 18446744073709551615u64
                                          {
                                              let size0: usize = (&psize)[0usize];
                                              let _letpattern1: (&mut [u8], &mut [u8]) =
                                                  out.split_at_mut(size0);
                                              let _out0: &[u8] = _letpattern1.0;
                                              let out1: &mut [u8] = _letpattern1.1;
                                              let mty: crate::cbordetver::cbor_det_int_kind =
                                                  crate::cbordetver::cbor_det_int_kind::UInt64;
                                              let c3: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_mk_int64(mty, 4u64);
                                              let res: crate::cbordetver::option__size_t =
                                                  crate::cbordetver::cbor_det_serialize(c3, out1);
                                              let res11: usize =
                                                  match res
                                                  {
                                                      crate::cbordetver::option__size_t::None =>
                                                        0usize,
                                                      crate::cbordetver::option__size_t::Some
                                                      { v: r }
                                                      => r,
                                                      _ => panic!("Incomplete pattern matching")
                                                  };
                                              if res11 > 0usize
                                              {
                                                  let size1: usize = size0.wrapping_add(res11);
                                                  let _letpattern2: (&mut [u8], &mut [u8]) =
                                                      out.split_at_mut(size1);
                                                  let _out01: &[u8] = _letpattern2.0;
                                                  let out2: &mut [u8] = _letpattern2.1;
                                                  let mut pcount1: [u64; 1] = [0u64; 1usize];
                                                  let mut psize1: [usize; 1] = [0usize; 1usize];
                                                  let res2: bool =
                                                      match c13
                                                      {
                                                          either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1::Inl
                                                          { v: c14 }
                                                          =>
                                                            if c14.len() == 0usize
                                                            { false }
                                                            else
                                                            {
                                                                let mut pres: [bool; 1] =
                                                                    [true; 1usize];
                                                                let mut pi: [usize; 1] =
                                                                    [0usize; 1usize];
                                                                let slen: usize = c14.len();
                                                                let res2: bool = (&pres)[0usize];
                                                                let i: usize = (&pi)[0usize];
                                                                let mut cond: bool =
                                                                    res2 && i < slen;
                                                                while
                                                                cond
                                                                {
                                                                    let i0: usize = (&pi)[0usize];
                                                                    let x: aux_env29_type_1 =
                                                                        c14[i0];
                                                                    let res20: bool =
                                                                        aux_env29_serialize_1(
                                                                            x,
                                                                            out2,
                                                                            &mut pcount1,
                                                                            &mut psize1
                                                                        );
                                                                    if res20
                                                                    {
                                                                        let i·: usize =
                                                                            i0.wrapping_add(1usize);
                                                                        (&mut pi)[0usize] = i·
                                                                    }
                                                                    else
                                                                    { (&mut pres)[0usize] = false };
                                                                    let res21: bool =
                                                                        (&pres)[0usize];
                                                                    let i1: usize = (&pi)[0usize];
                                                                    cond = res21 && i1 < slen
                                                                };
                                                                (&pres)[0usize]
                                                            },
                                                          either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1::Inr
                                                          { v: c23 }
                                                          =>
                                                            {
                                                                let em: bool =
                                                                    crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                                        c23.cddl_array_iterator_contents
                                                                    );
                                                                if em
                                                                { false }
                                                                else
                                                                {
                                                                    let
                                                                    mut
                                                                    pc:
                                                                    [array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1;
                                                                    1]
                                                                    =
                                                                        [c23; 1usize];
                                                                    let mut pres: [bool; 1] =
                                                                        [true; 1usize];
                                                                    let
                                                                    c4:
                                                                    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
                                                                    =
                                                                        (&pc)[0usize];
                                                                    let em1: bool =
                                                                        crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                                            c4.cddl_array_iterator_contents
                                                                        );
                                                                    let res2: bool =
                                                                        (&pres)[0usize];
                                                                    let mut cond: bool =
                                                                        res2 && ! em1;
                                                                    while
                                                                    cond
                                                                    {
                                                                        let
                                                                        i:
                                                                        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
                                                                        =
                                                                            (&pc)[0usize];
                                                                        let len0: u64 =
                                                                            crate::cbordetver::cbor_det_array_iterator_length(
                                                                                i.cddl_array_iterator_contents
                                                                            );
                                                                        let
                                                                        mut
                                                                        pj:
                                                                        [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw;
                                                                        1]
                                                                        =
                                                                            [i.cddl_array_iterator_contents;
                                                                                1usize];
                                                                        let discarded: bool =
                                                                            (i.cddl_array_iterator_impl_validate)(
                                                                                &mut pj
                                                                            );
                                                                        crate::lowstar::ignore::ignore::<bool>(
                                                                            discarded
                                                                        );
                                                                        let
                                                                        ji:
                                                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                                        =
                                                                            (&pj)[0usize];
                                                                        let len1: u64 =
                                                                            crate::cbordetver::cbor_det_array_iterator_length(
                                                                                ji
                                                                            );
                                                                        let
                                                                        j:
                                                                        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
                                                                        =
                                                                            array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
                                                                            {
                                                                                cddl_array_iterator_contents:
                                                                                ji,
                                                                                cddl_array_iterator_impl_validate:
                                                                                i.cddl_array_iterator_impl_validate,
                                                                                cddl_array_iterator_impl_parse:
                                                                                i.cddl_array_iterator_impl_parse
                                                                            };
                                                                        (&mut pc)[0usize] = j;
                                                                        let
                                                                        tri:
                                                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                                        =
                                                                            crate::cbordetver::cbor_det_array_iterator_truncate(
                                                                                i.cddl_array_iterator_contents,
                                                                                len0.wrapping_sub(
                                                                                    len1
                                                                                )
                                                                            );
                                                                        let x: aux_env29_type_1 =
                                                                            (i.cddl_array_iterator_impl_parse)(
                                                                                tri
                                                                            );
                                                                        let res20: bool =
                                                                            aux_env29_serialize_1(
                                                                                x,
                                                                                out2,
                                                                                &mut pcount1,
                                                                                &mut psize1
                                                                            );
                                                                        if ! res20
                                                                        {
                                                                            (&mut pres)[0usize] =
                                                                                false
                                                                        };
                                                                        let
                                                                        c40:
                                                                        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
                                                                        =
                                                                            (&pc)[0usize];
                                                                        let em10: bool =
                                                                            crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                                                c40.cddl_array_iterator_contents
                                                                            );
                                                                        let res21: bool =
                                                                            (&pres)[0usize];
                                                                        cond = res21 && ! em10
                                                                    };
                                                                    let ret: bool = (&pres)[0usize];
                                                                    if ret { ret } else { ret }
                                                                }
                                                            },
                                                          _ => panic!("Incomplete pattern matching")
                                                      };
                                                  let res21: usize =
                                                      if res2
                                                      {
                                                          let size: usize = (&psize1)[0usize];
                                                          let count1: u64 = (&pcount1)[0usize];
                                                          crate::cbordetver::cbor_det_serialize_array(
                                                              count1,
                                                              out2,
                                                              size
                                                          )
                                                      }
                                                      else
                                                      { 0usize };
                                                  if res21 > 0usize
                                                  {
                                                      let size2: usize = size1.wrapping_add(res21);
                                                      let _letpattern3: (&mut [u8], &mut [u8]) =
                                                          out.split_at_mut(size2);
                                                      let out012: &mut [u8] = _letpattern3.0;
                                                      let _out_rest: &[u8] = _letpattern3.1;
                                                      let res3: bool =
                                                          crate::cbordetver::cbor_det_serialize_map_insert(
                                                              out012,
                                                              size0,
                                                              size1
                                                          );
                                                      if res3
                                                      {
                                                          (&mut psize)[0usize] = size2;
                                                          (&mut pcount)[0usize] =
                                                              count.wrapping_add(1u64);
                                                          true
                                                      }
                                                      else
                                                      { false }
                                                  }
                                                  else
                                                  { false }
                                              }
                                              else
                                              { false }
                                          }
                                          else
                                          { false }
                                      },
                                    option__FStar_Pervasives_either__Pulse_Lib_Slice_slice·COSE_Format_aux_env29_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1::None
                                    => true,
                                    _ => panic!("Incomplete pattern matching")
                                }
                            }
                            else
                            { false }
                        };
                    if res1
                    {
                        match c21
                        {
                            option__Pulse_Lib_Slice_slice·uint8_t::Some { v: c12 } =>
                              {
                                  let count: u64 = (&pcount)[0usize];
                                  if count < 18446744073709551615u64
                                  {
                                      let size0: usize = (&psize)[0usize];
                                      let _letpattern1: (&mut [u8], &mut [u8]) =
                                          out.split_at_mut(size0);
                                      let _out0: &[u8] = _letpattern1.0;
                                      let out1: &mut [u8] = _letpattern1.1;
                                      let mty: crate::cbordetver::cbor_det_int_kind =
                                          crate::cbordetver::cbor_det_int_kind::UInt64;
                                      let c3: crate::cbordetveraux::cbor_raw =
                                          crate::cbordetver::cbor_det_mk_int64(mty, 5u64);
                                      let res: crate::cbordetver::option__size_t =
                                          crate::cbordetver::cbor_det_serialize(c3, out1);
                                      let res11: usize =
                                          match res
                                          {
                                              crate::cbordetver::option__size_t::None => 0usize,
                                              crate::cbordetver::option__size_t::Some { v: r } => r,
                                              _ => panic!("Incomplete pattern matching")
                                          };
                                      if res11 > 0usize
                                      {
                                          let size1: usize = size0.wrapping_add(res11);
                                          let _letpattern2: (&mut [u8], &mut [u8]) =
                                              out.split_at_mut(size1);
                                          let _out01: &[u8] = _letpattern2.0;
                                          let out2: &mut [u8] = _letpattern2.1;
                                          let res2: usize = serialize_bstr(c12, out2);
                                          if res2 > 0usize
                                          {
                                              let size2: usize = size1.wrapping_add(res2);
                                              let _letpattern3: (&mut [u8], &mut [u8]) =
                                                  out.split_at_mut(size2);
                                              let out012: &mut [u8] = _letpattern3.0;
                                              let _out_rest: &[u8] = _letpattern3.1;
                                              let res3: bool =
                                                  crate::cbordetver::cbor_det_serialize_map_insert(
                                                      out012,
                                                      size0,
                                                      size1
                                                  );
                                              if res3
                                              {
                                                  (&mut psize)[0usize] = size2;
                                                  (&mut pcount)[0usize] = count.wrapping_add(1u64);
                                                  true
                                              }
                                              else
                                              { false }
                                          }
                                          else
                                          { false }
                                      }
                                      else
                                      { false }
                                  }
                                  else
                                  { false }
                              },
                            option__Pulse_Lib_Slice_slice·uint8_t::None => true,
                            _ => panic!("Incomplete pattern matching")
                        }
                    }
                    else
                    { false }
                };
            if res1
            {
                match c2
                {
                    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw::Inl
                    { v: c11 }
                    =>
                      {
                          let discarded: [&[(evercddl_label, crate::cbordetveraux::cbor_raw)]; 1] =
                              [c11; 1usize];
                          crate::lowstar::ignore::ignore::<[&[(evercddl_label,
                          crate::cbordetveraux::cbor_raw)];
                          1]>(discarded);
                          let mut pres: [bool; 1] = [true; 1usize];
                          let mut pc: [&[(evercddl_label, crate::cbordetveraux::cbor_raw)]; 1] =
                              [c11; 1usize];
                          let em0: bool = c11.len() == 0usize;
                          let mut pem: [bool; 1] = [em0; 1usize];
                          let __anf1: bool = (&pres)[0usize];
                          let __anf0: bool = (&pem)[0usize];
                          let mut cond: bool = __anf1 && ! __anf0;
                          while
                          cond
                          {
                              let count: u64 = (&pcount)[0usize];
                              if count == 18446744073709551615u64
                              { (&mut pres)[0usize] = false }
                              else
                              {
                                  let count·: u64 = count.wrapping_add(1u64);
                                  let i: &[(evercddl_label, crate::cbordetveraux::cbor_raw)] =
                                      (&pc)[0usize];
                                  let res: (evercddl_label, crate::cbordetveraux::cbor_raw) =
                                      i[0usize];
                                  let
                                  _letpattern1:
                                  (&[(evercddl_label, crate::cbordetveraux::cbor_raw)],
                                  &[(evercddl_label, crate::cbordetveraux::cbor_raw)])
                                  =
                                      i.split_at(1usize);
                                  let
                                  _letpattern2: (evercddl_label, crate::cbordetveraux::cbor_raw)
                                  =
                                      {
                                          let
                                          _il: &[(evercddl_label, crate::cbordetveraux::cbor_raw)]
                                          =
                                              _letpattern1.0;
                                          let
                                          ir: &[(evercddl_label, crate::cbordetveraux::cbor_raw)]
                                          =
                                              _letpattern1.1;
                                          (&mut pc)[0usize] = ir;
                                          res
                                      };
                                  let ek: evercddl_label = _letpattern2.0;
                                  let ev: crate::cbordetveraux::cbor_raw = _letpattern2.1;
                                  let size0: usize = (&psize)[0usize];
                                  let _letpattern3: (&mut [u8], &mut [u8]) =
                                      out.split_at_mut(size0);
                                  let _tmp: &[u8] = _letpattern3.0;
                                  let out1: &mut [u8] = _letpattern3.1;
                                  let size1: usize = serialize_evercddl_label(ek, out1);
                                  if size1 == 0usize
                                  { (&mut pres)[0usize] = false }
                                  else
                                  {
                                      let _letpattern4: (&mut [u8], &mut [u8]) =
                                          out1.split_at_mut(size1);
                                      let out1·: &[u8] = _letpattern4.0;
                                      let out2: &mut [u8] = _letpattern4.1;
                                      let size2: usize = serialize_values(ev, out2);
                                      if size2 == 0usize
                                      { (&mut pres)[0usize] = false }
                                      else
                                      {
                                          let
                                          res2:
                                          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                          =
                                              crate::cbordetver::cbor_det_parse(out1·);
                                          let
                                          ock:
                                          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                          =
                                              match res2
                                              {
                                                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
                                                  =>
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None,
                                                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                  { v: pair }
                                                  =>
                                                    {
                                                        let c3: crate::cbordetveraux::cbor_raw =
                                                            pair.0;
                                                        let rem: &[u8] = pair.1;
                                                        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                        { v: (c3,rem) }
                                                    },
                                                  _ => panic!("Incomplete pattern matching")
                                              };
                                          match ock
                                          {
                                              crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                              { v: ck_ }
                                              =>
                                                {
                                                    let ck: crate::cbordetveraux::cbor_raw = ck_.0;
                                                    let _remk: &[u8] = ck_.1;
                                                    let _letpattern5: (&[u8], &[u8]) =
                                                        out2.split_at(size2);
                                                    let out2·: &[u8] = _letpattern5.0;
                                                    let _out2_tail: &[u8] = _letpattern5.1;
                                                    let
                                                    res3:
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                                    =
                                                        crate::cbordetver::cbor_det_parse(out2·);
                                                    let
                                                    ocv:
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                                    =
                                                        match res3
                                                        {
                                                            crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
                                                            =>
                                                              crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None,
                                                            crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                            { v: pair }
                                                            =>
                                                              {
                                                                  let
                                                                  c3: crate::cbordetveraux::cbor_raw
                                                                  =
                                                                      pair.0;
                                                                  let rem: &[u8] = pair.1;
                                                                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                                  { v: (c3,rem) }
                                                              },
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        };
                                                    match ocv
                                                    {
                                                        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                        { v: cv_ }
                                                        =>
                                                          {
                                                              let
                                                              cv: crate::cbordetveraux::cbor_raw
                                                              =
                                                                  cv_.0;
                                                              let _remv: &[u8] = cv_.1;
                                                              let
                                                              ce:
                                                              crate::cbordetveraux::cbor_map_entry
                                                              =
                                                                  crate::cbordetver::cbor_det_mk_map_entry(
                                                                      ck,
                                                                      cv
                                                                  );
                                                              let ex: bool =
                                                                  aux_env29_map_constraint_2(ce);
                                                              if ex
                                                              { (&mut pres)[0usize] = false }
                                                              else
                                                              {
                                                                  let size1·: usize =
                                                                      size0.wrapping_add(size1);
                                                                  let size2·: usize =
                                                                      size1·.wrapping_add(size2);
                                                                  let
                                                                  _letpattern6:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size2·);
                                                                  let out_: &mut [u8] =
                                                                      _letpattern6.0;
                                                                  let _tmp1: &[u8] = _letpattern6.1;
                                                                  let no_dup: bool =
                                                                      crate::cbordetver::cbor_det_serialize_map_insert(
                                                                          out_,
                                                                          size0,
                                                                          size1·
                                                                      );
                                                                  if no_dup
                                                                  {
                                                                      let
                                                                      __anf00:
                                                                      &[(evercddl_label,
                                                                      crate::cbordetveraux::cbor_raw)]
                                                                      =
                                                                          (&pc)[0usize];
                                                                      let __anf10: bool =
                                                                          __anf00.len() == 0usize;
                                                                      (&mut pem)[0usize] = __anf10;
                                                                      (&mut psize)[0usize] = size2·;
                                                                      (&mut pcount)[0usize] =
                                                                          count·
                                                                  }
                                                                  else
                                                                  { (&mut pres)[0usize] = false }
                                                              }
                                                          },
                                                        _ => panic!("Incomplete pattern matching")
                                                    }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          }
                                      }
                                  }
                              };
                              let __anf10: bool = (&pres)[0usize];
                              let __anf00: bool = (&pem)[0usize];
                              cond = __anf10 && ! __anf00
                          };
                          (&pres)[0usize]
                      },
                    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw::Inr
                    { v: c21 }
                    =>
                      {
                          let mut pres: [bool; 1] = [true; 1usize];
                          let
                          mut
                          pc:
                          [map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw;
                          1]
                          =
                              [c21; 1usize];
                          let
                          mut
                          pj:
                          [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry;
                          1]
                          =
                              [c21.cddl_map_iterator_contents; 1usize];
                          let mut pres1: [bool; 1] = [true; 1usize];
                          let
                          j:
                          crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                          =
                              (&pj)[0usize];
                          let test: bool = crate::cbordetver::cbor_det_map_iterator_is_empty(j);
                          let res: bool = (&pres1)[0usize];
                          let mut cond: bool = res && ! test;
                          while
                          cond
                          {
                              let elt: crate::cbordetveraux::cbor_map_entry =
                                  crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
                              let elt_key: crate::cbordetveraux::cbor_raw =
                                  crate::cbordetver::cbor_det_map_entry_key(elt);
                              let test_key: bool = (c21.cddl_map_iterator_impl_validate1)(elt_key);
                              if ! ! test_key
                              {
                                  let test_ex: bool = (c21.cddl_map_iterator_impl_validate_ex)(elt);
                                  if ! test_ex
                                  {
                                      let elt_value: crate::cbordetveraux::cbor_raw =
                                          crate::cbordetver::cbor_det_map_entry_value(elt);
                                      let test_value: bool =
                                          (c21.cddl_map_iterator_impl_validate2)(elt_value);
                                      (&mut pres1)[0usize] = ! test_value
                                  }
                              };
                              let
                              j0:
                              crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                              =
                                  (&pj)[0usize];
                              let test0: bool =
                                  crate::cbordetver::cbor_det_map_iterator_is_empty(j0);
                              let res0: bool = (&pres1)[0usize];
                              cond = res0 && ! test0
                          };
                          let em0: bool = (&pres1)[0usize];
                          let mut pem: [bool; 1] = [em0; 1usize];
                          let __anf1: bool = (&pres)[0usize];
                          let __anf0: bool = (&pem)[0usize];
                          let mut cond0: bool = __anf1 && ! __anf0;
                          while
                          cond0
                          {
                              let count: u64 = (&pcount)[0usize];
                              if count == 18446744073709551615u64
                              { (&mut pres)[0usize] = false }
                              else
                              {
                                  let count·: u64 = count.wrapping_add(1u64);
                                  let
                                  i:
                                  map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
                                  =
                                      (&pc)[0usize];
                                  let
                                  mut
                                  pj1:
                                  [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry;
                                  1]
                                  =
                                      [i.cddl_map_iterator_contents; 1usize];
                                  let hd0: crate::cbordetveraux::cbor_map_entry =
                                      crate::cbordetver::cbor_det_map_iterator_next(&mut pj1);
                                  let mut phd: [crate::cbordetveraux::cbor_map_entry; 1] =
                                      [hd0; 1usize];
                                  let hk0: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_key(hd0);
                                  let tk0: bool = (i.cddl_map_iterator_impl_validate1)(hk0);
                                  let hv0: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_value(hd0);
                                  let tv0: bool = (i.cddl_map_iterator_impl_validate2)(hv0);
                                  let te0: bool = (i.cddl_map_iterator_impl_validate_ex)(hd0);
                                  let mut pcont: [bool; 1] = [! tk0 || ! tv0 || te0; 1usize];
                                  while
                                  (&pcont)[0usize]
                                  {
                                      let hd: crate::cbordetveraux::cbor_map_entry =
                                          crate::cbordetver::cbor_det_map_iterator_next(&mut pj1);
                                      (&mut phd)[0usize] = hd;
                                      let hk: crate::cbordetveraux::cbor_raw =
                                          crate::cbordetver::cbor_det_map_entry_key(hd);
                                      let tk: bool = (i.cddl_map_iterator_impl_validate1)(hk);
                                      let hv: crate::cbordetveraux::cbor_raw =
                                          crate::cbordetver::cbor_det_map_entry_value(hd);
                                      let tv: bool = (i.cddl_map_iterator_impl_validate2)(hv);
                                      let te: bool = (i.cddl_map_iterator_impl_validate_ex)(hd);
                                      (&mut pcont)[0usize] = ! tk || ! tv || te
                                  };
                                  let hd: crate::cbordetveraux::cbor_map_entry = (&phd)[0usize];
                                  let hd_key: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_key(hd);
                                  let hd_key_res: evercddl_label =
                                      (i.cddl_map_iterator_impl_parse1)(hd_key);
                                  let hd_value: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_value(hd);
                                  let hd_value_res: crate::cbordetveraux::cbor_raw =
                                      (i.cddl_map_iterator_impl_parse2)(hd_value);
                                  let
                                  j0:
                                  crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                  =
                                      (&pj1)[0usize];
                                  let
                                  i·:
                                  map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
                                  =
                                      map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
                                      {
                                          cddl_map_iterator_contents: j0,
                                          cddl_map_iterator_impl_validate1:
                                          i.cddl_map_iterator_impl_validate1,
                                          cddl_map_iterator_impl_parse1:
                                          i.cddl_map_iterator_impl_parse1,
                                          cddl_map_iterator_impl_validate_ex:
                                          i.cddl_map_iterator_impl_validate_ex,
                                          cddl_map_iterator_impl_validate2:
                                          i.cddl_map_iterator_impl_validate2,
                                          cddl_map_iterator_impl_parse2:
                                          i.cddl_map_iterator_impl_parse2
                                      };
                                  (&mut pc)[0usize] = i·;
                                  let
                                  _letpattern1: (evercddl_label, crate::cbordetveraux::cbor_raw)
                                  =
                                      (hd_key_res,hd_value_res);
                                  let ek: evercddl_label = _letpattern1.0;
                                  let ev: crate::cbordetveraux::cbor_raw = _letpattern1.1;
                                  let size0: usize = (&psize)[0usize];
                                  let _letpattern2: (&mut [u8], &mut [u8]) =
                                      out.split_at_mut(size0);
                                  let _tmp: &[u8] = _letpattern2.0;
                                  let out1: &mut [u8] = _letpattern2.1;
                                  let size1: usize = serialize_evercddl_label(ek, out1);
                                  if size1 == 0usize
                                  { (&mut pres)[0usize] = false }
                                  else
                                  {
                                      let _letpattern3: (&mut [u8], &mut [u8]) =
                                          out1.split_at_mut(size1);
                                      let out1·: &[u8] = _letpattern3.0;
                                      let out2: &mut [u8] = _letpattern3.1;
                                      let size2: usize = serialize_values(ev, out2);
                                      if size2 == 0usize
                                      { (&mut pres)[0usize] = false }
                                      else
                                      {
                                          let
                                          res0:
                                          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                          =
                                              crate::cbordetver::cbor_det_parse(out1·);
                                          let
                                          ock:
                                          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                          =
                                              match res0
                                              {
                                                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
                                                  =>
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None,
                                                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                  { v: pair }
                                                  =>
                                                    {
                                                        let c3: crate::cbordetveraux::cbor_raw =
                                                            pair.0;
                                                        let rem: &[u8] = pair.1;
                                                        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                        { v: (c3,rem) }
                                                    },
                                                  _ => panic!("Incomplete pattern matching")
                                              };
                                          match ock
                                          {
                                              crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                              { v: ck_ }
                                              =>
                                                {
                                                    let ck: crate::cbordetveraux::cbor_raw = ck_.0;
                                                    let _remk: &[u8] = ck_.1;
                                                    let _letpattern4: (&[u8], &[u8]) =
                                                        out2.split_at(size2);
                                                    let out2·: &[u8] = _letpattern4.0;
                                                    let _out2_tail: &[u8] = _letpattern4.1;
                                                    let
                                                    res2:
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                                    =
                                                        crate::cbordetver::cbor_det_parse(out2·);
                                                    let
                                                    ocv:
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                                    =
                                                        match res2
                                                        {
                                                            crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
                                                            =>
                                                              crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None,
                                                            crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                            { v: pair }
                                                            =>
                                                              {
                                                                  let
                                                                  c3: crate::cbordetveraux::cbor_raw
                                                                  =
                                                                      pair.0;
                                                                  let rem: &[u8] = pair.1;
                                                                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                                  { v: (c3,rem) }
                                                              },
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        };
                                                    match ocv
                                                    {
                                                        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                        { v: cv_ }
                                                        =>
                                                          {
                                                              let
                                                              cv: crate::cbordetveraux::cbor_raw
                                                              =
                                                                  cv_.0;
                                                              let _remv: &[u8] = cv_.1;
                                                              let
                                                              ce:
                                                              crate::cbordetveraux::cbor_map_entry
                                                              =
                                                                  crate::cbordetver::cbor_det_mk_map_entry(
                                                                      ck,
                                                                      cv
                                                                  );
                                                              let ex: bool =
                                                                  aux_env29_map_constraint_2(ce);
                                                              if ex
                                                              { (&mut pres)[0usize] = false }
                                                              else
                                                              {
                                                                  let size1·: usize =
                                                                      size0.wrapping_add(size1);
                                                                  let size2·: usize =
                                                                      size1·.wrapping_add(size2);
                                                                  let
                                                                  _letpattern5:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size2·);
                                                                  let out_: &mut [u8] =
                                                                      _letpattern5.0;
                                                                  let _tmp1: &[u8] = _letpattern5.1;
                                                                  let no_dup: bool =
                                                                      crate::cbordetver::cbor_det_serialize_map_insert(
                                                                          out_,
                                                                          size0,
                                                                          size1·
                                                                      );
                                                                  if no_dup
                                                                  {
                                                                      let
                                                                      __anf00:
                                                                      map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
                                                                      =
                                                                          (&pc)[0usize];
                                                                      let
                                                                      mut
                                                                      pj2:
                                                                      [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry;
                                                                      1]
                                                                      =
                                                                          [__anf00.cddl_map_iterator_contents;
                                                                              1usize];
                                                                      let mut pres2: [bool; 1] =
                                                                          [true; 1usize];
                                                                      let
                                                                      j1:
                                                                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                                                      =
                                                                          (&pj2)[0usize];
                                                                      let test0: bool =
                                                                          crate::cbordetver::cbor_det_map_iterator_is_empty(
                                                                              j1
                                                                          );
                                                                      let res3: bool =
                                                                          (&pres2)[0usize];
                                                                      let mut cond1: bool =
                                                                          res3 && ! test0;
                                                                      while
                                                                      cond1
                                                                      {
                                                                          let
                                                                          elt:
                                                                          crate::cbordetveraux::cbor_map_entry
                                                                          =
                                                                              crate::cbordetver::cbor_det_map_iterator_next(
                                                                                  &mut pj2
                                                                              );
                                                                          let
                                                                          elt_key:
                                                                          crate::cbordetveraux::cbor_raw
                                                                          =
                                                                              crate::cbordetver::cbor_det_map_entry_key(
                                                                                  elt
                                                                              );
                                                                          let test_key: bool =
                                                                              (__anf00.cddl_map_iterator_impl_validate1)(
                                                                                  elt_key
                                                                              );
                                                                          if ! ! test_key
                                                                          {
                                                                              let test_ex: bool =
                                                                                  (__anf00.cddl_map_iterator_impl_validate_ex)(
                                                                                      elt
                                                                                  );
                                                                              if ! test_ex
                                                                              {
                                                                                  let
                                                                                  elt_value:
                                                                                  crate::cbordetveraux::cbor_raw
                                                                                  =
                                                                                      crate::cbordetver::cbor_det_map_entry_value(
                                                                                          elt
                                                                                      );
                                                                                  let
                                                                                  test_value: bool
                                                                                  =
                                                                                      (__anf00.cddl_map_iterator_impl_validate2)(
                                                                                          elt_value
                                                                                      );
                                                                                  (&mut pres2)[0usize] =
                                                                                      ! test_value
                                                                              }
                                                                          };
                                                                          let
                                                                          j10:
                                                                          crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                                                          =
                                                                              (&pj2)[0usize];
                                                                          let test1: bool =
                                                                              crate::cbordetver::cbor_det_map_iterator_is_empty(
                                                                                  j10
                                                                              );
                                                                          let res30: bool =
                                                                              (&pres2)[0usize];
                                                                          cond1 = res30 && ! test1
                                                                      };
                                                                      let __anf10: bool =
                                                                          (&pres2)[0usize];
                                                                      (&mut pem)[0usize] = __anf10;
                                                                      (&mut psize)[0usize] = size2·;
                                                                      (&mut pcount)[0usize] =
                                                                          count·
                                                                  }
                                                                  else
                                                                  { (&mut pres)[0usize] = false }
                                                              }
                                                          },
                                                        _ => panic!("Incomplete pattern matching")
                                                    }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          }
                                      }
                                  }
                              };
                              let __anf10: bool = (&pres)[0usize];
                              let __anf00: bool = (&pem)[0usize];
                              cond0 = __anf10 && ! __anf00
                          };
                          (&pres)[0usize]
                      },
                    _ => panic!("Incomplete pattern matching")
                }
            }
            else
            { false }
        };
    if res
    {
        let size: usize = (&psize)[0usize];
        let count: u64 = (&pcount)[0usize];
        crate::cbordetver::cbor_det_serialize_map(count, out, size)
    }
    else
    { 0usize }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_cose_key_generic···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (cose_key_generic <'a>, &'a [u8]) }
}

pub fn validate_and_parse_cose_key_generic <'a>(s: &'a [u8]) ->
    option__·COSE_Format_cose_key_generic···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·COSE_Format_cose_key_generic···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_cose_key_generic(rl);
              if test
              {
                  let x: cose_key_generic = parse_cose_key_generic(rl);
                  option__·COSE_Format_cose_key_generic···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_cose_key_generic···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn is_empty_iterate_array_aux_env29_type_1(
    i:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
) ->
    bool
{ crate::cbordetver::cbor_det_array_iterator_is_empty(i.cddl_array_iterator_contents) }

pub fn next_iterate_array_aux_env29_type_1 <'a>(
    pi:
    &'a mut
    [array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
    <'a>]
) ->
    aux_env29_type_1
    <'a>
{
    let
    i:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
    =
        pi[0usize];
    let len0: u64 =
        crate::cbordetver::cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
    let mut pj: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [i.cddl_array_iterator_contents; 1usize];
    let discarded: bool = (i.cddl_array_iterator_impl_validate)(&mut pj);
    crate::lowstar::ignore::ignore::<bool>(discarded);
    let ji: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pj)[0usize];
    let len1: u64 = crate::cbordetver::cbor_det_array_iterator_length(ji);
    let
    j:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
    =
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1
        {
            cddl_array_iterator_contents: ji,
            cddl_array_iterator_impl_validate: i.cddl_array_iterator_impl_validate,
            cddl_array_iterator_impl_parse: i.cddl_array_iterator_impl_parse
        };
    pi[0usize] = j;
    let tri: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(
            i.cddl_array_iterator_contents,
            len0.wrapping_sub(len1)
        );
    (i.cddl_array_iterator_impl_parse)(tri)
}

pub fn is_empty_iterate_map_evercddl_label_and_values(
    i:
    map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
) ->
    bool
{
    let mut pj: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry; 1] =
        [i.cddl_map_iterator_contents; 1usize];
    let mut pres: [bool; 1] = [true; 1usize];
    let j: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
        (&pj)[0usize];
    let test: bool = crate::cbordetver::cbor_det_map_iterator_is_empty(j);
    let res: bool = (&pres)[0usize];
    let mut cond: bool = res && ! test;
    while
    cond
    {
        let elt: crate::cbordetveraux::cbor_map_entry =
            crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
        let elt_key: crate::cbordetveraux::cbor_raw =
            crate::cbordetver::cbor_det_map_entry_key(elt);
        let test_key: bool = (i.cddl_map_iterator_impl_validate1)(elt_key);
        if ! ! test_key
        {
            let test_ex: bool = (i.cddl_map_iterator_impl_validate_ex)(elt);
            if ! test_ex
            {
                let elt_value: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_map_entry_value(elt);
                let test_value: bool = (i.cddl_map_iterator_impl_validate2)(elt_value);
                (&mut pres)[0usize] = ! test_value
            }
        };
        let j0: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
            (&pj)[0usize];
        let test0: bool = crate::cbordetver::cbor_det_map_iterator_is_empty(j0);
        let res0: bool = (&pres)[0usize];
        cond = res0 && ! test0
    };
    (&pres)[0usize]
}

pub fn next_iterate_map_evercddl_label_and_values <'a>(
    pi:
    &'a mut
    [map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
    <'a>]
) ->
    (evercddl_label <'a>, crate::cbordetveraux::cbor_raw <'a>)
{
    let
    i:
    map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
    =
        pi[0usize];
    let mut pj: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry; 1] =
        [i.cddl_map_iterator_contents; 1usize];
    let hd0: crate::cbordetveraux::cbor_map_entry =
        crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
    let mut phd: [crate::cbordetveraux::cbor_map_entry; 1] = [hd0; 1usize];
    let hk0: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(hd0);
    let tk0: bool = (i.cddl_map_iterator_impl_validate1)(hk0);
    let hv0: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_value(hd0);
    let tv0: bool = (i.cddl_map_iterator_impl_validate2)(hv0);
    let te0: bool = (i.cddl_map_iterator_impl_validate_ex)(hd0);
    let mut pcont: [bool; 1] = [! tk0 || ! tv0 || te0; 1usize];
    while
    (&pcont)[0usize]
    {
        let hd: crate::cbordetveraux::cbor_map_entry =
            crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
        (&mut phd)[0usize] = hd;
        let hk: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(hd);
        let tk: bool = (i.cddl_map_iterator_impl_validate1)(hk);
        let hv: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_value(hd);
        let tv: bool = (i.cddl_map_iterator_impl_validate2)(hv);
        let te: bool = (i.cddl_map_iterator_impl_validate_ex)(hd);
        (&mut pcont)[0usize] = ! tk || ! tv || te
    };
    let hd: crate::cbordetveraux::cbor_map_entry = (&phd)[0usize];
    let hd_key: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(hd);
    let hd_key_res: evercddl_label = (i.cddl_map_iterator_impl_parse1)(hd_key);
    let hd_value: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_value(hd);
    let hd_value_res: crate::cbordetveraux::cbor_raw = (i.cddl_map_iterator_impl_parse2)(hd_value);
    let j: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
        (&pj)[0usize];
    let
    i·:
    map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
    =
        map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
        {
            cddl_map_iterator_contents: j,
            cddl_map_iterator_impl_validate1: i.cddl_map_iterator_impl_validate1,
            cddl_map_iterator_impl_parse1: i.cddl_map_iterator_impl_parse1,
            cddl_map_iterator_impl_validate_ex: i.cddl_map_iterator_impl_validate_ex,
            cddl_map_iterator_impl_validate2: i.cddl_map_iterator_impl_validate2,
            cddl_map_iterator_impl_parse2: i.cddl_map_iterator_impl_parse2
        };
    pi[0usize] = i·;
    (hd_key_res,hd_value_res)
}

pub fn aux_env30_validate_1(
    pi: &mut [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw]
) ->
    bool
{
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = pi[0usize];
    let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i);
    if is_done
    { false }
    else
    {
        let c: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_array_iterator_next(pi);
        validate_cose_key_generic(c)
    }
}

pub type aux_env30_type_1_ugly <'a> = cose_key_generic <'a>;

pub type aux_env30_type_1 <'a> = cose_key_generic <'a>;

pub fn aux_env30_type_1_right <'a>(x1: cose_key_generic <'a>) -> cose_key_generic <'a> { x1 }

pub fn aux_env30_type_1_left <'a>(x4: cose_key_generic <'a>) -> cose_key_generic <'a> { x4 }

/**
Parser for aux_env30_type_1
*/
pub fn
aux_env30_parse_1
<'a>(c: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>) ->
    cose_key_generic
    <'a>
{
    let mut pc: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c; 1usize];
    let x: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
    parse_cose_key_generic(x)
}

/**
Serializer for aux_env30_type_1
*/
pub fn
aux_env30_serialize_1(
    c: cose_key_generic,
    out: &mut [u8],
    out_count: &mut [u64],
    out_size: &mut [usize]
) ->
    bool
{
    let count: u64 = out_count[0usize];
    if count < 18446744073709551615u64
    {
        let size: usize = out_size[0usize];
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
        let _out0: &[u8] = _letpattern.0;
        let out1: &mut [u8] = _letpattern.1;
        let size1: usize = serialize_cose_key_generic(c, out1);
        if size1 == 0usize
        { false }
        else
        {
            out_count[0usize] = count.wrapping_add(1u64);
            out_size[0usize] = size.wrapping_add(size1);
            true
        }
    }
    else
    { false }
}

pub fn validate_cose_keyset(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let ty: u8 = crate::cbordetver::cbor_det_major_type(c);
    if ty == crate::cbordetveraux::cbor_major_type_array
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
            match v
            {
                crate::cbordetver::cbor_det_view::Array { _0: a } =>
                  crate::cbordetver::cbor_det_array_iterator_start(a),
                _ => panic!("Incomplete pattern matching")
            };
        let mut pi: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
            [i; 1usize];
        let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
            (&pi)[0usize];
        let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
        let test1: bool =
            if is_done
            { false }
            else
            {
                let c1: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                validate_cose_key_generic(c1)
            };
        let b_success: bool =
            if test1
            {
                let mut pcont: [bool; 1] = [true; 1usize];
                while
                (&pcont)[0usize]
                {
                    let i11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                        (&pi)[0usize];
                    let i2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                        (&pi)[0usize];
                    let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
                    let cont: bool =
                        if is_done1
                        { false }
                        else
                        {
                            let c1: crate::cbordetveraux::cbor_raw =
                                crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                            validate_cose_key_generic(c1)
                        };
                    if ! cont
                    {
                        (&mut pi)[0usize] = i11;
                        (&mut pcont)[0usize] = false
                    }
                };
                true
            }
            else
            { false };
        if b_success
        {
            let i·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pi)[0usize];
            crate::cbordetver::cbor_det_array_iterator_is_empty(i·)
        }
        else
        { false }
    }
    else
    { false }
}

#[derive(PartialEq, Clone, Copy)]
pub struct
array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_key_generic
<'a>
{
    pub cddl_array_iterator_contents:
    crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>,
    pub cddl_array_iterator_impl_validate:
    fn (&mut [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw]) -> bool,
    pub cddl_array_iterator_impl_parse:
    for<'a1>
    fn
    (crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a1>)
    ->
    cose_key_generic
    <'a1>
}

#[derive(PartialEq, Clone, Copy)]
pub enum cose_keyset_ugly <'a>
{
    Inl { v: &'a [cose_key_generic <'a>] },
    Inr
    {
        v:
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_key_generic
        <'a>
    }
}

#[derive(PartialEq, Clone, Copy)]
enum cose_keyset_tags
{
    Mkcose_keyset0,
    Mkcose_keyset1
}

#[derive(PartialEq, Clone, Copy)]
pub enum cose_keyset <'a>
{
    Mkcose_keyset0 { _x0: &'a [cose_key_generic <'a>] },
    Mkcose_keyset1
    {
        _x0:
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_key_generic
        <'a>
    }
}

pub fn cose_keyset_right <'a>(x2: cose_keyset_ugly <'a>) -> cose_keyset <'a>
{
    match x2
    {
        cose_keyset_ugly::Inl { v: x3 } => cose_keyset::Mkcose_keyset0 { _x0: x3 },
        cose_keyset_ugly::Inr { v: x4 } => cose_keyset::Mkcose_keyset1 { _x0: x4 },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn cose_keyset_left <'a>(x8: cose_keyset <'a>) -> cose_keyset_ugly <'a>
{
    match x8
    {
        cose_keyset::Mkcose_keyset0 { _x0: x10 } => cose_keyset_ugly::Inl { v: x10 },
        cose_keyset::Mkcose_keyset1 { _x0: x12 } => cose_keyset_ugly::Inr { v: x12 },
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Parser for cose_keyset
*/
pub fn
parse_cose_keyset
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    cose_keyset
    <'a>
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let ar: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        match v
        {
            crate::cbordetver::cbor_det_view::Array { _0: a } =>
              crate::cbordetver::cbor_det_array_iterator_start(a),
            _ => panic!("Incomplete pattern matching")
        };
    let
    i:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_key_generic
    =
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_key_generic
        {
            cddl_array_iterator_contents: ar,
            cddl_array_iterator_impl_validate:
            aux_env30_validate_1
            as
            fn
            (&mut [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw])
            ->
            bool,
            cddl_array_iterator_impl_parse: aux_env30_parse_1
        };
    let res1: cose_keyset_ugly = cose_keyset_ugly::Inr { v: i };
    cose_keyset_right(res1)
}

/**
Serializer for cose_keyset
*/
pub fn
serialize_cose_keyset(c: cose_keyset, out: &mut [u8]) ->
    usize
{
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let res: bool =
        match cose_keyset_left(c)
        {
            cose_keyset_ugly::Inl { v: c1 } =>
              if c1.len() == 0usize
              { false }
              else
              {
                  let mut pres: [bool; 1] = [true; 1usize];
                  let mut pi: [usize; 1] = [0usize; 1usize];
                  let slen: usize = c1.len();
                  let res: bool = (&pres)[0usize];
                  let i: usize = (&pi)[0usize];
                  let mut cond: bool = res && i < slen;
                  while
                  cond
                  {
                      let i0: usize = (&pi)[0usize];
                      let x: cose_key_generic = c1[i0];
                      let res0: bool = aux_env30_serialize_1(x, out, &mut pcount, &mut psize);
                      if res0
                      {
                          let i·: usize = i0.wrapping_add(1usize);
                          (&mut pi)[0usize] = i·
                      }
                      else
                      { (&mut pres)[0usize] = false };
                      let res1: bool = (&pres)[0usize];
                      let i1: usize = (&pi)[0usize];
                      cond = res1 && i1 < slen
                  };
                  (&pres)[0usize]
              },
            cose_keyset_ugly::Inr { v: c2 } =>
              {
                  let em: bool =
                      crate::cbordetver::cbor_det_array_iterator_is_empty(
                          c2.cddl_array_iterator_contents
                      );
                  if em
                  { false }
                  else
                  {
                      let
                      mut
                      pc:
                      [array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_key_generic;
                      1]
                      =
                          [c2; 1usize];
                      let mut pres: [bool; 1] = [true; 1usize];
                      let
                      c1:
                      array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_key_generic
                      =
                          (&pc)[0usize];
                      let em1: bool =
                          crate::cbordetver::cbor_det_array_iterator_is_empty(
                              c1.cddl_array_iterator_contents
                          );
                      let res: bool = (&pres)[0usize];
                      let mut cond: bool = res && ! em1;
                      while
                      cond
                      {
                          let
                          i:
                          array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_key_generic
                          =
                              (&pc)[0usize];
                          let len0: u64 =
                              crate::cbordetver::cbor_det_array_iterator_length(
                                  i.cddl_array_iterator_contents
                              );
                          let
                          mut
                          pj:
                          [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
                          =
                              [i.cddl_array_iterator_contents; 1usize];
                          let discarded: bool = (i.cddl_array_iterator_impl_validate)(&mut pj);
                          crate::lowstar::ignore::ignore::<bool>(discarded);
                          let
                          ji: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                          =
                              (&pj)[0usize];
                          let len1: u64 = crate::cbordetver::cbor_det_array_iterator_length(ji);
                          let
                          j:
                          array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_key_generic
                          =
                              array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_key_generic
                              {
                                  cddl_array_iterator_contents: ji,
                                  cddl_array_iterator_impl_validate:
                                  i.cddl_array_iterator_impl_validate,
                                  cddl_array_iterator_impl_parse: i.cddl_array_iterator_impl_parse
                              };
                          (&mut pc)[0usize] = j;
                          let
                          tri: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                          =
                              crate::cbordetver::cbor_det_array_iterator_truncate(
                                  i.cddl_array_iterator_contents,
                                  len0.wrapping_sub(len1)
                              );
                          let x: cose_key_generic = (i.cddl_array_iterator_impl_parse)(tri);
                          let res0: bool = aux_env30_serialize_1(x, out, &mut pcount, &mut psize);
                          if ! res0 { (&mut pres)[0usize] = false };
                          let
                          c10:
                          array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_key_generic
                          =
                              (&pc)[0usize];
                          let em10: bool =
                              crate::cbordetver::cbor_det_array_iterator_is_empty(
                                  c10.cddl_array_iterator_contents
                              );
                          let res1: bool = (&pres)[0usize];
                          cond = res1 && ! em10
                      };
                      let ret: bool = (&pres)[0usize];
                      if ret { ret } else { ret }
                  }
              },
            _ => panic!("Incomplete pattern matching")
        };
    if res
    {
        let size: usize = (&psize)[0usize];
        let count: u64 = (&pcount)[0usize];
        crate::cbordetver::cbor_det_serialize_array(count, out, size)
    }
    else
    { 0usize }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_cose_keyset···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (cose_keyset <'a>, &'a [u8]) }
}

pub fn validate_and_parse_cose_keyset <'a>(s: &'a [u8]) ->
    option__·COSE_Format_cose_keyset···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·COSE_Format_cose_keyset···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_cose_keyset(rl);
              if test
              {
                  let x: cose_keyset = parse_cose_keyset(rl);
                  option__·COSE_Format_cose_keyset···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_cose_keyset···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn is_empty_iterate_array_aux_env30_type_1(
    i:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_key_generic
) ->
    bool
{ crate::cbordetver::cbor_det_array_iterator_is_empty(i.cddl_array_iterator_contents) }

pub fn next_iterate_array_aux_env30_type_1 <'a>(
    pi:
    &'a mut
    [array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_key_generic
    <'a>]
) ->
    cose_key_generic
    <'a>
{
    let
    i:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_key_generic
    =
        pi[0usize];
    let len0: u64 =
        crate::cbordetver::cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
    let mut pj: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [i.cddl_array_iterator_contents; 1usize];
    let discarded: bool = (i.cddl_array_iterator_impl_validate)(&mut pj);
    crate::lowstar::ignore::ignore::<bool>(discarded);
    let ji: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pj)[0usize];
    let len1: u64 = crate::cbordetver::cbor_det_array_iterator_length(ji);
    let
    j:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_key_generic
    =
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_key_generic
        {
            cddl_array_iterator_contents: ji,
            cddl_array_iterator_impl_validate: i.cddl_array_iterator_impl_validate,
            cddl_array_iterator_impl_parse: i.cddl_array_iterator_impl_parse
        };
    pi[0usize] = j;
    let tri: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(
            i.cddl_array_iterator_contents,
            len0.wrapping_sub(len1)
        );
    (i.cddl_array_iterator_impl_parse)(tri)
}

pub fn aux_env31_map_constraint_1(x: crate::cbordetveraux::cbor_map_entry) -> bool
{
    let k: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
    let mt: u8 = crate::cbordetver::cbor_det_major_type(k);
    let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;
    let testk: bool =
        if is_uint
        {
            let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(k);
            let i: u64 =
                match v
                {
                    crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                    _ => panic!("Incomplete pattern matching")
                };
            i == 1u64
        }
        else
        { false };
    let test: bool =
        if testk
        {
            let discarded: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_map_entry_value(x);
            crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(discarded);
            true
        }
        else
        { false };
    let test1: bool =
        if test
        { true }
        else
        {
            let k1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
            let mt1: u8 = crate::cbordetver::cbor_det_major_type(k1);
            let is_uint1: bool = mt1 == crate::cbordetveraux::cbor_major_type_neg_int64;
            let testk1: bool =
                if is_uint1
                {
                    let v: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(k1);
                    let i: u64 =
                        match v
                        {
                            crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                            _ => panic!("Incomplete pattern matching")
                        };
                    i == 0u64
                }
                else
                { false };
            if testk1
            {
                let discarded: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_map_entry_value(x);
                crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(discarded);
                true
            }
            else
            { false }
        };
    let test2: bool =
        if test1
        { true }
        else
        {
            let k1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
            let mt1: u8 = crate::cbordetver::cbor_det_major_type(k1);
            let is_uint1: bool = mt1 == crate::cbordetveraux::cbor_major_type_neg_int64;
            let testk1: bool =
                if is_uint1
                {
                    let v: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(k1);
                    let i: u64 =
                        match v
                        {
                            crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                            _ => panic!("Incomplete pattern matching")
                        };
                    i == 1u64
                }
                else
                { false };
            if testk1
            {
                let discarded: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_map_entry_value(x);
                crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(discarded);
                true
            }
            else
            { false }
        };
    if test2
    { true }
    else
    {
        let k1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
        let mt1: u8 = crate::cbordetver::cbor_det_major_type(k1);
        let is_uint1: bool = mt1 == crate::cbordetveraux::cbor_major_type_neg_int64;
        let testk1: bool =
            if is_uint1
            {
                let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(k1);
                let i: u64 =
                    match v
                    {
                        crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                        _ => panic!("Incomplete pattern matching")
                    };
                i == 3u64
            }
            else
            { false };
        if testk1
        {
            let discarded: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_map_entry_value(x);
            crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(discarded);
            true
        }
        else
        { false }
    }
}

pub fn validate_cose_key_okp(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let ty: u8 = crate::cbordetver::cbor_det_major_type(c);
    if ty == crate::cbordetveraux::cbor_major_type_map
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let rem0: u64 =
            match v
            {
                crate::cbordetver::cbor_det_view::Map { _0: a } =>
                  crate::cbordetver::cbor_det_map_length(a),
                _ => panic!("Incomplete pattern matching")
            };
        let mut remaining: [u64; 1] = [rem0; 1usize];
        let mty: crate::cbordetver::cbor_det_int_kind =
            crate::cbordetver::cbor_det_int_kind::UInt64;
        let c1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty, 1u64);
        let x·: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let mg: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
            match x·
            {
                crate::cbordetver::cbor_det_view::Map { _0: m } =>
                  crate::cbordetver::cbor_det_map_get(m, c1),
                _ => panic!("Incomplete pattern matching")
            };
        let res1: crate::cbordetveraux::impl_map_group_result =
            match mg
            {
                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: cv } =>
                  {
                      let mt: u8 = crate::cbordetver::cbor_det_major_type(cv);
                      let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;
                      let check_value: bool =
                          if is_uint
                          {
                              let v1: crate::cbordetver::cbor_det_view =
                                  crate::cbordetver::cbor_det_destruct(cv);
                              let i: u64 =
                                  match v1
                                  {
                                      crate::cbordetver::cbor_det_view::Int64 { value: res, .. } =>
                                        res,
                                      _ => panic!("Incomplete pattern matching")
                                  };
                              i == 1u64
                          }
                          else
                          { false };
                      if check_value
                      {
                          let i1: u64 = (&remaining)[0usize];
                          let i2: u64 = i1.wrapping_sub(1u64);
                          (&mut remaining)[0usize] = i2;
                          crate::cbordetveraux::impl_map_group_result::MGOK
                      }
                      else
                      { crate::cbordetveraux::impl_map_group_result::MGCutFail }
                  },
                _ => panic!("Incomplete pattern matching")
            };
        let res11: crate::cbordetveraux::impl_map_group_result =
            match res1
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  {
                      let mty1: crate::cbordetver::cbor_det_int_kind =
                          if
                          crate::cbordetveraux::cbor_major_type_neg_int64
                          ==
                          crate::cbordetveraux::cbor_major_type_uint64
                          { crate::cbordetver::cbor_det_int_kind::UInt64 }
                          else
                          { crate::cbordetver::cbor_det_int_kind::NegInt64 };
                      let c2: crate::cbordetveraux::cbor_raw =
                          crate::cbordetver::cbor_det_mk_int64(mty1, 0u64);
                      let x·1: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let mg1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                          match x·1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: m } =>
                                crate::cbordetver::cbor_det_map_get(m, c2),
                              _ => panic!("Incomplete pattern matching")
                          };
                      match mg1
                      {
                          crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                            crate::cbordetveraux::impl_map_group_result::MGFail,
                          crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: cv } =>
                            {
                                let test: bool = validate_int(cv);
                                let check_value: bool = if test { true } else { validate_tstr(cv) };
                                if check_value
                                {
                                    let i1: u64 = (&remaining)[0usize];
                                    let i2: u64 = i1.wrapping_sub(1u64);
                                    (&mut remaining)[0usize] = i2;
                                    crate::cbordetveraux::impl_map_group_result::MGOK
                                }
                                else
                                { crate::cbordetveraux::impl_map_group_result::MGCutFail }
                            },
                          _ => panic!("Incomplete pattern matching")
                      }
                  },
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        let res12: crate::cbordetveraux::impl_map_group_result =
            match res11
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  {
                      let i0: u64 = (&remaining)[0usize];
                      let mty1: crate::cbordetver::cbor_det_int_kind =
                          if
                          crate::cbordetveraux::cbor_major_type_neg_int64
                          ==
                          crate::cbordetveraux::cbor_major_type_uint64
                          { crate::cbordetver::cbor_det_int_kind::UInt64 }
                          else
                          { crate::cbordetver::cbor_det_int_kind::NegInt64 };
                      let c2: crate::cbordetveraux::cbor_raw =
                          crate::cbordetver::cbor_det_mk_int64(mty1, 1u64);
                      let x·1: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let mg1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                          match x·1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: m } =>
                                crate::cbordetver::cbor_det_map_get(m, c2),
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res12: crate::cbordetveraux::impl_map_group_result =
                          match mg1
                          {
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                                crate::cbordetveraux::impl_map_group_result::MGFail,
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                              { v: cv }
                              =>
                                {
                                    let check_value: bool = validate_bstr(cv);
                                    if check_value
                                    {
                                        let i1: u64 = (&remaining)[0usize];
                                        let i2: u64 = i1.wrapping_sub(1u64);
                                        (&mut remaining)[0usize] = i2;
                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                    }
                                    else
                                    { crate::cbordetveraux::impl_map_group_result::MGCutFail }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      match res12
                      {
                          crate::cbordetveraux::impl_map_group_result::MGOK =>
                            crate::cbordetveraux::impl_map_group_result::MGOK,
                          crate::cbordetveraux::impl_map_group_result::MGFail =>
                            {
                                (&mut remaining)[0usize] = i0;
                                crate::cbordetveraux::impl_map_group_result::MGOK
                            },
                          crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                            crate::cbordetveraux::impl_map_group_result::MGCutFail,
                          _ => panic!("Precondition of the function most likely violated")
                      }
                  },
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        let res13: crate::cbordetveraux::impl_map_group_result =
            match res12
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  {
                      let i0: u64 = (&remaining)[0usize];
                      let mty1: crate::cbordetver::cbor_det_int_kind =
                          if
                          crate::cbordetveraux::cbor_major_type_neg_int64
                          ==
                          crate::cbordetveraux::cbor_major_type_uint64
                          { crate::cbordetver::cbor_det_int_kind::UInt64 }
                          else
                          { crate::cbordetver::cbor_det_int_kind::NegInt64 };
                      let c2: crate::cbordetveraux::cbor_raw =
                          crate::cbordetver::cbor_det_mk_int64(mty1, 3u64);
                      let x·1: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let mg1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                          match x·1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: m } =>
                                crate::cbordetver::cbor_det_map_get(m, c2),
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res13: crate::cbordetveraux::impl_map_group_result =
                          match mg1
                          {
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                                crate::cbordetveraux::impl_map_group_result::MGFail,
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                              { v: cv }
                              =>
                                {
                                    let check_value: bool = validate_bstr(cv);
                                    if check_value
                                    {
                                        let i1: u64 = (&remaining)[0usize];
                                        let i2: u64 = i1.wrapping_sub(1u64);
                                        (&mut remaining)[0usize] = i2;
                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                    }
                                    else
                                    { crate::cbordetveraux::impl_map_group_result::MGCutFail }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      match res13
                      {
                          crate::cbordetveraux::impl_map_group_result::MGOK =>
                            crate::cbordetveraux::impl_map_group_result::MGOK,
                          crate::cbordetveraux::impl_map_group_result::MGFail =>
                            {
                                (&mut remaining)[0usize] = i0;
                                crate::cbordetveraux::impl_map_group_result::MGOK
                            },
                          crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                            crate::cbordetveraux::impl_map_group_result::MGCutFail,
                          _ => panic!("Precondition of the function most likely violated")
                      }
                  },
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        let res: crate::cbordetveraux::impl_map_group_result =
            match res13
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  {
                      let v1: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let
                      j0:
                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                      =
                          match v1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: a } =>
                                crate::cbordetver::cbor_det_map_iterator_start(a),
                              _ => panic!("Incomplete pattern matching")
                          };
                      let
                      mut
                      pj:
                      [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry;
                      1]
                      =
                          [j0; 1usize];
                      let
                      j: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                      =
                          (&pj)[0usize];
                      let is_empty: bool = crate::cbordetver::cbor_det_map_iterator_is_empty(j);
                      let mut cond: bool = ! is_empty;
                      while
                      cond
                      {
                          let chd: crate::cbordetveraux::cbor_map_entry =
                              crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
                          let k: crate::cbordetveraux::cbor_raw =
                              crate::cbordetver::cbor_det_map_entry_key(chd);
                          let testk: bool = validate_evercddl_label(k);
                          let test: bool =
                              if testk
                              {
                                  let v2: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_value(chd);
                                  validate_values(v2)
                              }
                              else
                              { false };
                          let test1: bool =
                              if test
                              {
                                  let k1: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_key(chd);
                                  let mt: u8 = crate::cbordetver::cbor_det_major_type(k1);
                                  let is_uint: bool =
                                      mt == crate::cbordetveraux::cbor_major_type_uint64;
                                  let testk1: bool =
                                      if is_uint
                                      {
                                          let v2: crate::cbordetver::cbor_det_view =
                                              crate::cbordetver::cbor_det_destruct(k1);
                                          let i: u64 =
                                              match v2
                                              {
                                                  crate::cbordetver::cbor_det_view::Int64
                                                  { value: res, .. }
                                                  => res,
                                                  _ => panic!("Incomplete pattern matching")
                                              };
                                          i == 1u64
                                      }
                                      else
                                      { false };
                                  let test1: bool =
                                      if testk1
                                      {
                                          let discarded: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_value(chd);
                                          crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(
                                              discarded
                                          );
                                          true
                                      }
                                      else
                                      { false };
                                  let test2: bool =
                                      if test1
                                      { true }
                                      else
                                      {
                                          let k2: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(chd);
                                          let mt1: u8 = crate::cbordetver::cbor_det_major_type(k2);
                                          let is_uint1: bool =
                                              mt1 == crate::cbordetveraux::cbor_major_type_neg_int64;
                                          let testk2: bool =
                                              if is_uint1
                                              {
                                                  let v2: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(k2);
                                                  let i: u64 =
                                                      match v2
                                                      {
                                                          crate::cbordetver::cbor_det_view::Int64
                                                          { value: res, .. }
                                                          => res,
                                                          _ => panic!("Incomplete pattern matching")
                                                      };
                                                  i == 0u64
                                              }
                                              else
                                              { false };
                                          if testk2
                                          {
                                              let discarded: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(chd);
                                              crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(
                                                  discarded
                                              );
                                              true
                                          }
                                          else
                                          { false }
                                      };
                                  let test3: bool =
                                      if test2
                                      { true }
                                      else
                                      {
                                          let k2: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(chd);
                                          let mt1: u8 = crate::cbordetver::cbor_det_major_type(k2);
                                          let is_uint1: bool =
                                              mt1 == crate::cbordetveraux::cbor_major_type_neg_int64;
                                          let testk2: bool =
                                              if is_uint1
                                              {
                                                  let v2: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(k2);
                                                  let i: u64 =
                                                      match v2
                                                      {
                                                          crate::cbordetver::cbor_det_view::Int64
                                                          { value: res, .. }
                                                          => res,
                                                          _ => panic!("Incomplete pattern matching")
                                                      };
                                                  i == 1u64
                                              }
                                              else
                                              { false };
                                          if testk2
                                          {
                                              let discarded: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(chd);
                                              crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(
                                                  discarded
                                              );
                                              true
                                          }
                                          else
                                          { false }
                                      };
                                  let test4: bool =
                                      if test3
                                      { true }
                                      else
                                      {
                                          let k2: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(chd);
                                          let mt1: u8 = crate::cbordetver::cbor_det_major_type(k2);
                                          let is_uint1: bool =
                                              mt1 == crate::cbordetveraux::cbor_major_type_neg_int64;
                                          let testk2: bool =
                                              if is_uint1
                                              {
                                                  let v2: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(k2);
                                                  let i: u64 =
                                                      match v2
                                                      {
                                                          crate::cbordetver::cbor_det_view::Int64
                                                          { value: res, .. }
                                                          => res,
                                                          _ => panic!("Incomplete pattern matching")
                                                      };
                                                  i == 3u64
                                              }
                                              else
                                              { false };
                                          if testk2
                                          {
                                              let discarded: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(chd);
                                              crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(
                                                  discarded
                                              );
                                              true
                                          }
                                          else
                                          { false }
                                      };
                                  ! test4
                              }
                              else
                              { false };
                          let test2: bool = ! test1;
                          if ! test2
                          {
                              let i: u64 = (&remaining)[0usize];
                              let i·: u64 = i.wrapping_sub(1u64);
                              (&mut remaining)[0usize] = i·
                          };
                          let
                          j1:
                          crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                          =
                              (&pj)[0usize];
                          let is_empty0: bool =
                              crate::cbordetver::cbor_det_map_iterator_is_empty(j1);
                          cond = ! is_empty0
                      };
                      crate::cbordetveraux::impl_map_group_result::MGOK
                  },
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        match res
        {
            crate::cbordetveraux::impl_map_group_result::MGOK =>
              {
                  let rem: u64 = (&remaining)[0usize];
                  rem == 0u64
              },
            crate::cbordetveraux::impl_map_group_result::MGFail => false,
            crate::cbordetveraux::impl_map_group_result::MGCutFail => false,
            _ => panic!("Precondition of the function most likely violated")
        }
    }
    else
    { false }
}

#[derive(PartialEq, Clone, Copy)]
pub struct cose_key_okp <'a>
{
    pub intkeyneg1: either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t <'a>,
    pub intkeyneg2: option__Pulse_Lib_Slice_slice·uint8_t <'a>,
    pub intkeyneg4: option__Pulse_Lib_Slice_slice·uint8_t <'a>,
    pub _x0:
    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
}

pub fn cose_key_okp_right <'a>(
    x5:
    (((((), either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t <'a>),
    option__Pulse_Lib_Slice_slice·uint8_t
    <'a>),
    option__Pulse_Lib_Slice_slice·uint8_t
    <'a>),
    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
    <'a>)
) ->
    cose_key_okp
    <'a>
{
    match x5
    {
        ((((_x6,x7),x8),x9),x10) =>
          cose_key_okp { intkeyneg1: x7, intkeyneg2: x8, intkeyneg4: x9, _x0: x10 }
    }
}

pub fn cose_key_okp_left <'a>(x12: cose_key_okp <'a>) ->
    (((((), either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t <'a>),
    option__Pulse_Lib_Slice_slice·uint8_t
    <'a>),
    option__Pulse_Lib_Slice_slice·uint8_t
    <'a>),
    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
    <'a>)
{ (((((),x12.intkeyneg1),x12.intkeyneg2),x12.intkeyneg4),x12._x0) }

/**
Parser for cose_key_okp
*/
pub fn
parse_cose_key_okp
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    cose_key_okp
    <'a>
{
    let mty: crate::cbordetver::cbor_det_int_kind = crate::cbordetver::cbor_det_int_kind::UInt64;
    let c1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty, 1u64);
    let x·: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let ow: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match x·
        {
            crate::cbordetver::cbor_det_view::Map { _0: m } =>
              crate::cbordetver::cbor_det_map_get(m, c1),
            _ => panic!("Incomplete pattern matching")
        };
    crate::lowstar::ignore::ignore::<crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw>(ow);
    let mty1: crate::cbordetver::cbor_det_int_kind =
        if
        crate::cbordetveraux::cbor_major_type_neg_int64
        ==
        crate::cbordetveraux::cbor_major_type_uint64
        { crate::cbordetver::cbor_det_int_kind::UInt64 }
        else
        { crate::cbordetver::cbor_det_int_kind::NegInt64 };
    let c2: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty1, 0u64);
    let x·1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let ow1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match x·1
        {
            crate::cbordetver::cbor_det_view::Map { _0: m } =>
              crate::cbordetver::cbor_det_map_get(m, c2),
            _ => panic!("Incomplete pattern matching")
        };
    let w2: either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t =
        match ow1
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
              {
                  let test: bool = validate_int(w);
                  if test
                  {
                      let res: evercddl_int = parse_int(w);
                      either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t::Inl
                      { v: res }
                  }
                  else
                  {
                      let res: &[u8] = parse_tstr(w);
                      either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t::Inr
                      { v: res }
                  }
              },
            _ => panic!("Incomplete pattern matching")
        };
    let w11: ((), either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t) = ((),w2);
    let discarded: [u64; 1] = [0u64; 1usize];
    crate::lowstar::ignore::ignore::<[u64; 1]>(discarded);
    let mty2: crate::cbordetver::cbor_det_int_kind =
        if
        crate::cbordetveraux::cbor_major_type_neg_int64
        ==
        crate::cbordetveraux::cbor_major_type_uint64
        { crate::cbordetver::cbor_det_int_kind::UInt64 }
        else
        { crate::cbordetver::cbor_det_int_kind::NegInt64 };
    let c3: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty2, 1u64);
    let x·2: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let mg: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match x·2
        {
            crate::cbordetver::cbor_det_view::Map { _0: m } =>
              crate::cbordetver::cbor_det_map_get(m, c3),
            _ => panic!("Incomplete pattern matching")
        };
    let test1: crate::cbordetveraux::impl_map_group_result =
        match mg
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
              crate::cbordetveraux::impl_map_group_result::MGFail,
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: cv } =>
              {
                  let check_value: bool = validate_bstr(cv);
                  if check_value
                  { crate::cbordetveraux::impl_map_group_result::MGOK }
                  else
                  { crate::cbordetveraux::impl_map_group_result::MGCutFail }
              },
            _ => panic!("Incomplete pattern matching")
        };
    let w21: option__Pulse_Lib_Slice_slice·uint8_t =
        if
        match test1
        {
            crate::cbordetveraux::impl_map_group_result::MGOK => true,
            _tmp => false,
            _ => panic!("Incomplete pattern matching")
        }
        {
            let mty3: crate::cbordetver::cbor_det_int_kind =
                if
                crate::cbordetveraux::cbor_major_type_neg_int64
                ==
                crate::cbordetveraux::cbor_major_type_uint64
                { crate::cbordetver::cbor_det_int_kind::UInt64 }
                else
                { crate::cbordetver::cbor_det_int_kind::NegInt64 };
            let c4: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty3, 1u64);
            let x·3: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let ow2: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match x·3
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m } =>
                      crate::cbordetver::cbor_det_map_get(m, c4),
                    _ => panic!("Incomplete pattern matching")
                };
            let w12: &[u8] =
                match ow2
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      parse_bstr(w),
                    _ => panic!("Incomplete pattern matching")
                };
            option__Pulse_Lib_Slice_slice·uint8_t::Some { v: w12 }
        }
        else
        { option__Pulse_Lib_Slice_slice·uint8_t::None };
    let
    w12:
    (((), either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t),
    option__Pulse_Lib_Slice_slice·uint8_t)
    =
        (w11,w21);
    let discarded1: [u64; 1] = [0u64; 1usize];
    crate::lowstar::ignore::ignore::<[u64; 1]>(discarded1);
    let mty3: crate::cbordetver::cbor_det_int_kind =
        if
        crate::cbordetveraux::cbor_major_type_neg_int64
        ==
        crate::cbordetveraux::cbor_major_type_uint64
        { crate::cbordetver::cbor_det_int_kind::UInt64 }
        else
        { crate::cbordetver::cbor_det_int_kind::NegInt64 };
    let c4: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty3, 3u64);
    let x·3: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let mg1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match x·3
        {
            crate::cbordetver::cbor_det_view::Map { _0: m } =>
              crate::cbordetver::cbor_det_map_get(m, c4),
            _ => panic!("Incomplete pattern matching")
        };
    let test11: crate::cbordetveraux::impl_map_group_result =
        match mg1
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
              crate::cbordetveraux::impl_map_group_result::MGFail,
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: cv } =>
              {
                  let check_value: bool = validate_bstr(cv);
                  if check_value
                  { crate::cbordetveraux::impl_map_group_result::MGOK }
                  else
                  { crate::cbordetveraux::impl_map_group_result::MGCutFail }
              },
            _ => panic!("Incomplete pattern matching")
        };
    let w22: option__Pulse_Lib_Slice_slice·uint8_t =
        if
        match test11
        {
            crate::cbordetveraux::impl_map_group_result::MGOK => true,
            _tmp => false,
            _ => panic!("Incomplete pattern matching")
        }
        {
            let mty4: crate::cbordetver::cbor_det_int_kind =
                if
                crate::cbordetveraux::cbor_major_type_neg_int64
                ==
                crate::cbordetveraux::cbor_major_type_uint64
                { crate::cbordetver::cbor_det_int_kind::UInt64 }
                else
                { crate::cbordetver::cbor_det_int_kind::NegInt64 };
            let c5: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty4, 3u64);
            let x·4: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let ow2: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match x·4
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m } =>
                      crate::cbordetver::cbor_det_map_get(m, c5),
                    _ => panic!("Incomplete pattern matching")
                };
            let w13: &[u8] =
                match ow2
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      parse_bstr(w),
                    _ => panic!("Incomplete pattern matching")
                };
            option__Pulse_Lib_Slice_slice·uint8_t::Some { v: w13 }
        }
        else
        { option__Pulse_Lib_Slice_slice·uint8_t::None };
    let
    w13:
    ((((), either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t),
    option__Pulse_Lib_Slice_slice·uint8_t),
    option__Pulse_Lib_Slice_slice·uint8_t)
    =
        (w12,w22);
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
        match v
        {
            crate::cbordetver::cbor_det_view::Map { _0: a } =>
              crate::cbordetver::cbor_det_map_iterator_start(a),
            _ => panic!("Incomplete pattern matching")
        };
    let
    rres:
    map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
    =
        map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
        {
            cddl_map_iterator_contents: i,
            cddl_map_iterator_impl_validate1:
            validate_evercddl_label as fn (crate::cbordetveraux::cbor_raw) -> bool,
            cddl_map_iterator_impl_parse1: parse_evercddl_label,
            cddl_map_iterator_impl_validate_ex:
            aux_env31_map_constraint_1 as fn (crate::cbordetveraux::cbor_map_entry) -> bool,
            cddl_map_iterator_impl_validate2:
            validate_values as fn (crate::cbordetveraux::cbor_raw) -> bool,
            cddl_map_iterator_impl_parse2: parse_values
        };
    let
    w23:
    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
    =
        either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw::Inr
        { v: rres };
    let
    res1:
    (((((), either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t),
    option__Pulse_Lib_Slice_slice·uint8_t),
    option__Pulse_Lib_Slice_slice·uint8_t),
    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw)
    =
        (w13,w23);
    cose_key_okp_right(res1)
}

/**
Serializer for cose_key_okp
*/
pub fn
serialize_cose_key_okp(c: cose_key_okp, out: &mut [u8]) ->
    usize
{
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let
    _letpattern:
    (((((), either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t),
    option__Pulse_Lib_Slice_slice·uint8_t),
    option__Pulse_Lib_Slice_slice·uint8_t),
    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw)
    =
        cose_key_okp_left(c);
    let res: bool =
        {
            let
            c1:
            ((((), either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t),
            option__Pulse_Lib_Slice_slice·uint8_t),
            option__Pulse_Lib_Slice_slice·uint8_t)
            =
                _letpattern.0;
            let
            c2:
            either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
            =
                _letpattern.1;
            let res1: bool =
                {
                    let
                    c11:
                    (((), either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t),
                    option__Pulse_Lib_Slice_slice·uint8_t)
                    =
                        c1.0;
                    let c21: option__Pulse_Lib_Slice_slice·uint8_t = c1.1;
                    let res1: bool =
                        {
                            let
                            c12:
                            ((), either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t)
                            =
                                c11.0;
                            let c22: option__Pulse_Lib_Slice_slice·uint8_t = c11.1;
                            let res1: bool =
                                {
                                    c12.0;
                                    let
                                    c23:
                                    either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t
                                    =
                                        c12.1;
                                    let count: u64 = (&pcount)[0usize];
                                    let res1: bool =
                                        if count < 18446744073709551615u64
                                        {
                                            let size0: usize = (&psize)[0usize];
                                            let _letpattern1: (&mut [u8], &mut [u8]) =
                                                out.split_at_mut(size0);
                                            let _out0: &[u8] = _letpattern1.0;
                                            let out1: &mut [u8] = _letpattern1.1;
                                            let mty: crate::cbordetver::cbor_det_int_kind =
                                                crate::cbordetver::cbor_det_int_kind::UInt64;
                                            let c3: crate::cbordetveraux::cbor_raw =
                                                crate::cbordetver::cbor_det_mk_int64(mty, 1u64);
                                            let res: crate::cbordetver::option__size_t =
                                                crate::cbordetver::cbor_det_serialize(c3, out1);
                                            let res1: usize =
                                                match res
                                                {
                                                    crate::cbordetver::option__size_t::None =>
                                                      0usize,
                                                    crate::cbordetver::option__size_t::Some
                                                    { v: r }
                                                    => r,
                                                    _ => panic!("Incomplete pattern matching")
                                                };
                                            if res1 > 0usize
                                            {
                                                let size1: usize = size0.wrapping_add(res1);
                                                let _letpattern2: (&mut [u8], &mut [u8]) =
                                                    out.split_at_mut(size1);
                                                let _out01: &[u8] = _letpattern2.0;
                                                let out2: &mut [u8] = _letpattern2.1;
                                                let mty1: crate::cbordetver::cbor_det_int_kind =
                                                    crate::cbordetver::cbor_det_int_kind::UInt64;
                                                let c4: crate::cbordetveraux::cbor_raw =
                                                    crate::cbordetver::cbor_det_mk_int64(mty1, 1u64);
                                                let res2: crate::cbordetver::option__size_t =
                                                    crate::cbordetver::cbor_det_serialize(c4, out2);
                                                let res21: usize =
                                                    match res2
                                                    {
                                                        crate::cbordetver::option__size_t::None =>
                                                          0usize,
                                                        crate::cbordetver::option__size_t::Some
                                                        { v: r }
                                                        => r,
                                                        _ => panic!("Incomplete pattern matching")
                                                    };
                                                if res21 > 0usize
                                                {
                                                    let size2: usize = size1.wrapping_add(res21);
                                                    let _letpattern3: (&mut [u8], &mut [u8]) =
                                                        out.split_at_mut(size2);
                                                    let out012: &mut [u8] = _letpattern3.0;
                                                    let _out_rest: &[u8] = _letpattern3.1;
                                                    let res3: bool =
                                                        crate::cbordetver::cbor_det_serialize_map_insert(
                                                            out012,
                                                            size0,
                                                            size1
                                                        );
                                                    if res3
                                                    {
                                                        (&mut psize)[0usize] = size2;
                                                        (&mut pcount)[0usize] =
                                                            count.wrapping_add(1u64);
                                                        true
                                                    }
                                                    else
                                                    { false }
                                                }
                                                else
                                                { false }
                                            }
                                            else
                                            { false }
                                        }
                                        else
                                        { false };
                                    if res1
                                    {
                                        let count1: u64 = (&pcount)[0usize];
                                        if count1 < 18446744073709551615u64
                                        {
                                            let size0: usize = (&psize)[0usize];
                                            let _letpattern1: (&mut [u8], &mut [u8]) =
                                                out.split_at_mut(size0);
                                            let _out0: &[u8] = _letpattern1.0;
                                            let out1: &mut [u8] = _letpattern1.1;
                                            let mty: crate::cbordetver::cbor_det_int_kind =
                                                if
                                                crate::cbordetveraux::cbor_major_type_neg_int64
                                                ==
                                                crate::cbordetveraux::cbor_major_type_uint64
                                                { crate::cbordetver::cbor_det_int_kind::UInt64 }
                                                else
                                                { crate::cbordetver::cbor_det_int_kind::NegInt64 };
                                            let c3: crate::cbordetveraux::cbor_raw =
                                                crate::cbordetver::cbor_det_mk_int64(mty, 0u64);
                                            let res: crate::cbordetver::option__size_t =
                                                crate::cbordetver::cbor_det_serialize(c3, out1);
                                            let res11: usize =
                                                match res
                                                {
                                                    crate::cbordetver::option__size_t::None =>
                                                      0usize,
                                                    crate::cbordetver::option__size_t::Some
                                                    { v: r }
                                                    => r,
                                                    _ => panic!("Incomplete pattern matching")
                                                };
                                            if res11 > 0usize
                                            {
                                                let size1: usize = size0.wrapping_add(res11);
                                                let _letpattern2: (&mut [u8], &mut [u8]) =
                                                    out.split_at_mut(size1);
                                                let _out01: &[u8] = _letpattern2.0;
                                                let out2: &mut [u8] = _letpattern2.1;
                                                let res2: usize =
                                                    match c23
                                                    {
                                                        either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t::Inl
                                                        { v: c14 }
                                                        => serialize_int(c14, out2),
                                                        either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t::Inr
                                                        { v: c24 }
                                                        => serialize_tstr(c24, out2),
                                                        _ => panic!("Incomplete pattern matching")
                                                    };
                                                if res2 > 0usize
                                                {
                                                    let size2: usize = size1.wrapping_add(res2);
                                                    let _letpattern3: (&mut [u8], &mut [u8]) =
                                                        out.split_at_mut(size2);
                                                    let out012: &mut [u8] = _letpattern3.0;
                                                    let _out_rest: &[u8] = _letpattern3.1;
                                                    let res3: bool =
                                                        crate::cbordetver::cbor_det_serialize_map_insert(
                                                            out012,
                                                            size0,
                                                            size1
                                                        );
                                                    if res3
                                                    {
                                                        (&mut psize)[0usize] = size2;
                                                        (&mut pcount)[0usize] =
                                                            count1.wrapping_add(1u64);
                                                        true
                                                    }
                                                    else
                                                    { false }
                                                }
                                                else
                                                { false }
                                            }
                                            else
                                            { false }
                                        }
                                        else
                                        { false }
                                    }
                                    else
                                    { false }
                                };
                            if res1
                            {
                                match c22
                                {
                                    option__Pulse_Lib_Slice_slice·uint8_t::Some { v: c13 } =>
                                      {
                                          let count: u64 = (&pcount)[0usize];
                                          if count < 18446744073709551615u64
                                          {
                                              let size0: usize = (&psize)[0usize];
                                              let _letpattern1: (&mut [u8], &mut [u8]) =
                                                  out.split_at_mut(size0);
                                              let _out0: &[u8] = _letpattern1.0;
                                              let out1: &mut [u8] = _letpattern1.1;
                                              let mty: crate::cbordetver::cbor_det_int_kind =
                                                  if
                                                  crate::cbordetveraux::cbor_major_type_neg_int64
                                                  ==
                                                  crate::cbordetveraux::cbor_major_type_uint64
                                                  { crate::cbordetver::cbor_det_int_kind::UInt64 }
                                                  else
                                                  { crate::cbordetver::cbor_det_int_kind::NegInt64 };
                                              let c3: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_mk_int64(mty, 1u64);
                                              let res: crate::cbordetver::option__size_t =
                                                  crate::cbordetver::cbor_det_serialize(c3, out1);
                                              let res11: usize =
                                                  match res
                                                  {
                                                      crate::cbordetver::option__size_t::None =>
                                                        0usize,
                                                      crate::cbordetver::option__size_t::Some
                                                      { v: r }
                                                      => r,
                                                      _ => panic!("Incomplete pattern matching")
                                                  };
                                              if res11 > 0usize
                                              {
                                                  let size1: usize = size0.wrapping_add(res11);
                                                  let _letpattern2: (&mut [u8], &mut [u8]) =
                                                      out.split_at_mut(size1);
                                                  let _out01: &[u8] = _letpattern2.0;
                                                  let out2: &mut [u8] = _letpattern2.1;
                                                  let res2: usize = serialize_bstr(c13, out2);
                                                  if res2 > 0usize
                                                  {
                                                      let size2: usize = size1.wrapping_add(res2);
                                                      let _letpattern3: (&mut [u8], &mut [u8]) =
                                                          out.split_at_mut(size2);
                                                      let out012: &mut [u8] = _letpattern3.0;
                                                      let _out_rest: &[u8] = _letpattern3.1;
                                                      let res3: bool =
                                                          crate::cbordetver::cbor_det_serialize_map_insert(
                                                              out012,
                                                              size0,
                                                              size1
                                                          );
                                                      if res3
                                                      {
                                                          (&mut psize)[0usize] = size2;
                                                          (&mut pcount)[0usize] =
                                                              count.wrapping_add(1u64);
                                                          true
                                                      }
                                                      else
                                                      { false }
                                                  }
                                                  else
                                                  { false }
                                              }
                                              else
                                              { false }
                                          }
                                          else
                                          { false }
                                      },
                                    option__Pulse_Lib_Slice_slice·uint8_t::None => true,
                                    _ => panic!("Incomplete pattern matching")
                                }
                            }
                            else
                            { false }
                        };
                    if res1
                    {
                        match c21
                        {
                            option__Pulse_Lib_Slice_slice·uint8_t::Some { v: c12 } =>
                              {
                                  let count: u64 = (&pcount)[0usize];
                                  if count < 18446744073709551615u64
                                  {
                                      let size0: usize = (&psize)[0usize];
                                      let _letpattern1: (&mut [u8], &mut [u8]) =
                                          out.split_at_mut(size0);
                                      let _out0: &[u8] = _letpattern1.0;
                                      let out1: &mut [u8] = _letpattern1.1;
                                      let mty: crate::cbordetver::cbor_det_int_kind =
                                          if
                                          crate::cbordetveraux::cbor_major_type_neg_int64
                                          ==
                                          crate::cbordetveraux::cbor_major_type_uint64
                                          { crate::cbordetver::cbor_det_int_kind::UInt64 }
                                          else
                                          { crate::cbordetver::cbor_det_int_kind::NegInt64 };
                                      let c3: crate::cbordetveraux::cbor_raw =
                                          crate::cbordetver::cbor_det_mk_int64(mty, 3u64);
                                      let res: crate::cbordetver::option__size_t =
                                          crate::cbordetver::cbor_det_serialize(c3, out1);
                                      let res11: usize =
                                          match res
                                          {
                                              crate::cbordetver::option__size_t::None => 0usize,
                                              crate::cbordetver::option__size_t::Some { v: r } => r,
                                              _ => panic!("Incomplete pattern matching")
                                          };
                                      if res11 > 0usize
                                      {
                                          let size1: usize = size0.wrapping_add(res11);
                                          let _letpattern2: (&mut [u8], &mut [u8]) =
                                              out.split_at_mut(size1);
                                          let _out01: &[u8] = _letpattern2.0;
                                          let out2: &mut [u8] = _letpattern2.1;
                                          let res2: usize = serialize_bstr(c12, out2);
                                          if res2 > 0usize
                                          {
                                              let size2: usize = size1.wrapping_add(res2);
                                              let _letpattern3: (&mut [u8], &mut [u8]) =
                                                  out.split_at_mut(size2);
                                              let out012: &mut [u8] = _letpattern3.0;
                                              let _out_rest: &[u8] = _letpattern3.1;
                                              let res3: bool =
                                                  crate::cbordetver::cbor_det_serialize_map_insert(
                                                      out012,
                                                      size0,
                                                      size1
                                                  );
                                              if res3
                                              {
                                                  (&mut psize)[0usize] = size2;
                                                  (&mut pcount)[0usize] = count.wrapping_add(1u64);
                                                  true
                                              }
                                              else
                                              { false }
                                          }
                                          else
                                          { false }
                                      }
                                      else
                                      { false }
                                  }
                                  else
                                  { false }
                              },
                            option__Pulse_Lib_Slice_slice·uint8_t::None => true,
                            _ => panic!("Incomplete pattern matching")
                        }
                    }
                    else
                    { false }
                };
            if res1
            {
                match c2
                {
                    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw::Inl
                    { v: c11 }
                    =>
                      {
                          let discarded: [&[(evercddl_label, crate::cbordetveraux::cbor_raw)]; 1] =
                              [c11; 1usize];
                          crate::lowstar::ignore::ignore::<[&[(evercddl_label,
                          crate::cbordetveraux::cbor_raw)];
                          1]>(discarded);
                          let mut pres: [bool; 1] = [true; 1usize];
                          let mut pc: [&[(evercddl_label, crate::cbordetveraux::cbor_raw)]; 1] =
                              [c11; 1usize];
                          let em0: bool = c11.len() == 0usize;
                          let mut pem: [bool; 1] = [em0; 1usize];
                          let __anf1: bool = (&pres)[0usize];
                          let __anf0: bool = (&pem)[0usize];
                          let mut cond: bool = __anf1 && ! __anf0;
                          while
                          cond
                          {
                              let count: u64 = (&pcount)[0usize];
                              if count == 18446744073709551615u64
                              { (&mut pres)[0usize] = false }
                              else
                              {
                                  let count·: u64 = count.wrapping_add(1u64);
                                  let i: &[(evercddl_label, crate::cbordetveraux::cbor_raw)] =
                                      (&pc)[0usize];
                                  let res: (evercddl_label, crate::cbordetveraux::cbor_raw) =
                                      i[0usize];
                                  let
                                  _letpattern1:
                                  (&[(evercddl_label, crate::cbordetveraux::cbor_raw)],
                                  &[(evercddl_label, crate::cbordetveraux::cbor_raw)])
                                  =
                                      i.split_at(1usize);
                                  let
                                  _letpattern2: (evercddl_label, crate::cbordetveraux::cbor_raw)
                                  =
                                      {
                                          let
                                          _il: &[(evercddl_label, crate::cbordetveraux::cbor_raw)]
                                          =
                                              _letpattern1.0;
                                          let
                                          ir: &[(evercddl_label, crate::cbordetveraux::cbor_raw)]
                                          =
                                              _letpattern1.1;
                                          (&mut pc)[0usize] = ir;
                                          res
                                      };
                                  let ek: evercddl_label = _letpattern2.0;
                                  let ev: crate::cbordetveraux::cbor_raw = _letpattern2.1;
                                  let size0: usize = (&psize)[0usize];
                                  let _letpattern3: (&mut [u8], &mut [u8]) =
                                      out.split_at_mut(size0);
                                  let _tmp: &[u8] = _letpattern3.0;
                                  let out1: &mut [u8] = _letpattern3.1;
                                  let size1: usize = serialize_evercddl_label(ek, out1);
                                  if size1 == 0usize
                                  { (&mut pres)[0usize] = false }
                                  else
                                  {
                                      let _letpattern4: (&mut [u8], &mut [u8]) =
                                          out1.split_at_mut(size1);
                                      let out1·: &[u8] = _letpattern4.0;
                                      let out2: &mut [u8] = _letpattern4.1;
                                      let size2: usize = serialize_values(ev, out2);
                                      if size2 == 0usize
                                      { (&mut pres)[0usize] = false }
                                      else
                                      {
                                          let
                                          res2:
                                          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                          =
                                              crate::cbordetver::cbor_det_parse(out1·);
                                          let
                                          ock:
                                          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                          =
                                              match res2
                                              {
                                                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
                                                  =>
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None,
                                                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                  { v: pair }
                                                  =>
                                                    {
                                                        let c3: crate::cbordetveraux::cbor_raw =
                                                            pair.0;
                                                        let rem: &[u8] = pair.1;
                                                        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                        { v: (c3,rem) }
                                                    },
                                                  _ => panic!("Incomplete pattern matching")
                                              };
                                          match ock
                                          {
                                              crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                              { v: ck_ }
                                              =>
                                                {
                                                    let ck: crate::cbordetveraux::cbor_raw = ck_.0;
                                                    let _remk: &[u8] = ck_.1;
                                                    let _letpattern5: (&[u8], &[u8]) =
                                                        out2.split_at(size2);
                                                    let out2·: &[u8] = _letpattern5.0;
                                                    let _out2_tail: &[u8] = _letpattern5.1;
                                                    let
                                                    res3:
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                                    =
                                                        crate::cbordetver::cbor_det_parse(out2·);
                                                    let
                                                    ocv:
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                                    =
                                                        match res3
                                                        {
                                                            crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
                                                            =>
                                                              crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None,
                                                            crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                            { v: pair }
                                                            =>
                                                              {
                                                                  let
                                                                  c3: crate::cbordetveraux::cbor_raw
                                                                  =
                                                                      pair.0;
                                                                  let rem: &[u8] = pair.1;
                                                                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                                  { v: (c3,rem) }
                                                              },
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        };
                                                    match ocv
                                                    {
                                                        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                        { v: cv_ }
                                                        =>
                                                          {
                                                              let
                                                              cv: crate::cbordetveraux::cbor_raw
                                                              =
                                                                  cv_.0;
                                                              let _remv: &[u8] = cv_.1;
                                                              let
                                                              ce:
                                                              crate::cbordetveraux::cbor_map_entry
                                                              =
                                                                  crate::cbordetver::cbor_det_mk_map_entry(
                                                                      ck,
                                                                      cv
                                                                  );
                                                              let ex: bool =
                                                                  aux_env31_map_constraint_1(ce);
                                                              if ex
                                                              { (&mut pres)[0usize] = false }
                                                              else
                                                              {
                                                                  let size1·: usize =
                                                                      size0.wrapping_add(size1);
                                                                  let size2·: usize =
                                                                      size1·.wrapping_add(size2);
                                                                  let
                                                                  _letpattern6:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size2·);
                                                                  let out_: &mut [u8] =
                                                                      _letpattern6.0;
                                                                  let _tmp1: &[u8] = _letpattern6.1;
                                                                  let no_dup: bool =
                                                                      crate::cbordetver::cbor_det_serialize_map_insert(
                                                                          out_,
                                                                          size0,
                                                                          size1·
                                                                      );
                                                                  if no_dup
                                                                  {
                                                                      let
                                                                      __anf00:
                                                                      &[(evercddl_label,
                                                                      crate::cbordetveraux::cbor_raw)]
                                                                      =
                                                                          (&pc)[0usize];
                                                                      let __anf10: bool =
                                                                          __anf00.len() == 0usize;
                                                                      (&mut pem)[0usize] = __anf10;
                                                                      (&mut psize)[0usize] = size2·;
                                                                      (&mut pcount)[0usize] =
                                                                          count·
                                                                  }
                                                                  else
                                                                  { (&mut pres)[0usize] = false }
                                                              }
                                                          },
                                                        _ => panic!("Incomplete pattern matching")
                                                    }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          }
                                      }
                                  }
                              };
                              let __anf10: bool = (&pres)[0usize];
                              let __anf00: bool = (&pem)[0usize];
                              cond = __anf10 && ! __anf00
                          };
                          (&pres)[0usize]
                      },
                    either__Pulse_Lib_Slice_slice··COSE_Format_evercddl_label···CBOR_Pulse_Raw_Type_cbor_raw·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw::Inr
                    { v: c21 }
                    =>
                      {
                          let mut pres: [bool; 1] = [true; 1usize];
                          let
                          mut
                          pc:
                          [map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw;
                          1]
                          =
                              [c21; 1usize];
                          let
                          mut
                          pj:
                          [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry;
                          1]
                          =
                              [c21.cddl_map_iterator_contents; 1usize];
                          let mut pres1: [bool; 1] = [true; 1usize];
                          let
                          j:
                          crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                          =
                              (&pj)[0usize];
                          let test: bool = crate::cbordetver::cbor_det_map_iterator_is_empty(j);
                          let res: bool = (&pres1)[0usize];
                          let mut cond: bool = res && ! test;
                          while
                          cond
                          {
                              let elt: crate::cbordetveraux::cbor_map_entry =
                                  crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
                              let elt_key: crate::cbordetveraux::cbor_raw =
                                  crate::cbordetver::cbor_det_map_entry_key(elt);
                              let test_key: bool = (c21.cddl_map_iterator_impl_validate1)(elt_key);
                              if ! ! test_key
                              {
                                  let test_ex: bool = (c21.cddl_map_iterator_impl_validate_ex)(elt);
                                  if ! test_ex
                                  {
                                      let elt_value: crate::cbordetveraux::cbor_raw =
                                          crate::cbordetver::cbor_det_map_entry_value(elt);
                                      let test_value: bool =
                                          (c21.cddl_map_iterator_impl_validate2)(elt_value);
                                      (&mut pres1)[0usize] = ! test_value
                                  }
                              };
                              let
                              j0:
                              crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                              =
                                  (&pj)[0usize];
                              let test0: bool =
                                  crate::cbordetver::cbor_det_map_iterator_is_empty(j0);
                              let res0: bool = (&pres1)[0usize];
                              cond = res0 && ! test0
                          };
                          let em0: bool = (&pres1)[0usize];
                          let mut pem: [bool; 1] = [em0; 1usize];
                          let __anf1: bool = (&pres)[0usize];
                          let __anf0: bool = (&pem)[0usize];
                          let mut cond0: bool = __anf1 && ! __anf0;
                          while
                          cond0
                          {
                              let count: u64 = (&pcount)[0usize];
                              if count == 18446744073709551615u64
                              { (&mut pres)[0usize] = false }
                              else
                              {
                                  let count·: u64 = count.wrapping_add(1u64);
                                  let
                                  i:
                                  map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
                                  =
                                      (&pc)[0usize];
                                  let
                                  mut
                                  pj1:
                                  [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry;
                                  1]
                                  =
                                      [i.cddl_map_iterator_contents; 1usize];
                                  let hd0: crate::cbordetveraux::cbor_map_entry =
                                      crate::cbordetver::cbor_det_map_iterator_next(&mut pj1);
                                  let mut phd: [crate::cbordetveraux::cbor_map_entry; 1] =
                                      [hd0; 1usize];
                                  let hk0: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_key(hd0);
                                  let tk0: bool = (i.cddl_map_iterator_impl_validate1)(hk0);
                                  let hv0: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_value(hd0);
                                  let tv0: bool = (i.cddl_map_iterator_impl_validate2)(hv0);
                                  let te0: bool = (i.cddl_map_iterator_impl_validate_ex)(hd0);
                                  let mut pcont: [bool; 1] = [! tk0 || ! tv0 || te0; 1usize];
                                  while
                                  (&pcont)[0usize]
                                  {
                                      let hd: crate::cbordetveraux::cbor_map_entry =
                                          crate::cbordetver::cbor_det_map_iterator_next(&mut pj1);
                                      (&mut phd)[0usize] = hd;
                                      let hk: crate::cbordetveraux::cbor_raw =
                                          crate::cbordetver::cbor_det_map_entry_key(hd);
                                      let tk: bool = (i.cddl_map_iterator_impl_validate1)(hk);
                                      let hv: crate::cbordetveraux::cbor_raw =
                                          crate::cbordetver::cbor_det_map_entry_value(hd);
                                      let tv: bool = (i.cddl_map_iterator_impl_validate2)(hv);
                                      let te: bool = (i.cddl_map_iterator_impl_validate_ex)(hd);
                                      (&mut pcont)[0usize] = ! tk || ! tv || te
                                  };
                                  let hd: crate::cbordetveraux::cbor_map_entry = (&phd)[0usize];
                                  let hd_key: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_key(hd);
                                  let hd_key_res: evercddl_label =
                                      (i.cddl_map_iterator_impl_parse1)(hd_key);
                                  let hd_value: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_value(hd);
                                  let hd_value_res: crate::cbordetveraux::cbor_raw =
                                      (i.cddl_map_iterator_impl_parse2)(hd_value);
                                  let
                                  j0:
                                  crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                  =
                                      (&pj1)[0usize];
                                  let
                                  i·:
                                  map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
                                  =
                                      map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
                                      {
                                          cddl_map_iterator_contents: j0,
                                          cddl_map_iterator_impl_validate1:
                                          i.cddl_map_iterator_impl_validate1,
                                          cddl_map_iterator_impl_parse1:
                                          i.cddl_map_iterator_impl_parse1,
                                          cddl_map_iterator_impl_validate_ex:
                                          i.cddl_map_iterator_impl_validate_ex,
                                          cddl_map_iterator_impl_validate2:
                                          i.cddl_map_iterator_impl_validate2,
                                          cddl_map_iterator_impl_parse2:
                                          i.cddl_map_iterator_impl_parse2
                                      };
                                  (&mut pc)[0usize] = i·;
                                  let
                                  _letpattern1: (evercddl_label, crate::cbordetveraux::cbor_raw)
                                  =
                                      (hd_key_res,hd_value_res);
                                  let ek: evercddl_label = _letpattern1.0;
                                  let ev: crate::cbordetveraux::cbor_raw = _letpattern1.1;
                                  let size0: usize = (&psize)[0usize];
                                  let _letpattern2: (&mut [u8], &mut [u8]) =
                                      out.split_at_mut(size0);
                                  let _tmp: &[u8] = _letpattern2.0;
                                  let out1: &mut [u8] = _letpattern2.1;
                                  let size1: usize = serialize_evercddl_label(ek, out1);
                                  if size1 == 0usize
                                  { (&mut pres)[0usize] = false }
                                  else
                                  {
                                      let _letpattern3: (&mut [u8], &mut [u8]) =
                                          out1.split_at_mut(size1);
                                      let out1·: &[u8] = _letpattern3.0;
                                      let out2: &mut [u8] = _letpattern3.1;
                                      let size2: usize = serialize_values(ev, out2);
                                      if size2 == 0usize
                                      { (&mut pres)[0usize] = false }
                                      else
                                      {
                                          let
                                          res0:
                                          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                          =
                                              crate::cbordetver::cbor_det_parse(out1·);
                                          let
                                          ock:
                                          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                          =
                                              match res0
                                              {
                                                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
                                                  =>
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None,
                                                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                  { v: pair }
                                                  =>
                                                    {
                                                        let c3: crate::cbordetveraux::cbor_raw =
                                                            pair.0;
                                                        let rem: &[u8] = pair.1;
                                                        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                        { v: (c3,rem) }
                                                    },
                                                  _ => panic!("Incomplete pattern matching")
                                              };
                                          match ock
                                          {
                                              crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                              { v: ck_ }
                                              =>
                                                {
                                                    let ck: crate::cbordetveraux::cbor_raw = ck_.0;
                                                    let _remk: &[u8] = ck_.1;
                                                    let _letpattern4: (&[u8], &[u8]) =
                                                        out2.split_at(size2);
                                                    let out2·: &[u8] = _letpattern4.0;
                                                    let _out2_tail: &[u8] = _letpattern4.1;
                                                    let
                                                    res2:
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                                    =
                                                        crate::cbordetver::cbor_det_parse(out2·);
                                                    let
                                                    ocv:
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                                    =
                                                        match res2
                                                        {
                                                            crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
                                                            =>
                                                              crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None,
                                                            crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                            { v: pair }
                                                            =>
                                                              {
                                                                  let
                                                                  c3: crate::cbordetveraux::cbor_raw
                                                                  =
                                                                      pair.0;
                                                                  let rem: &[u8] = pair.1;
                                                                  crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                                  { v: (c3,rem) }
                                                              },
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        };
                                                    match ocv
                                                    {
                                                        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                        { v: cv_ }
                                                        =>
                                                          {
                                                              let
                                                              cv: crate::cbordetveraux::cbor_raw
                                                              =
                                                                  cv_.0;
                                                              let _remv: &[u8] = cv_.1;
                                                              let
                                                              ce:
                                                              crate::cbordetveraux::cbor_map_entry
                                                              =
                                                                  crate::cbordetver::cbor_det_mk_map_entry(
                                                                      ck,
                                                                      cv
                                                                  );
                                                              let ex: bool =
                                                                  aux_env31_map_constraint_1(ce);
                                                              if ex
                                                              { (&mut pres)[0usize] = false }
                                                              else
                                                              {
                                                                  let size1·: usize =
                                                                      size0.wrapping_add(size1);
                                                                  let size2·: usize =
                                                                      size1·.wrapping_add(size2);
                                                                  let
                                                                  _letpattern5:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size2·);
                                                                  let out_: &mut [u8] =
                                                                      _letpattern5.0;
                                                                  let _tmp1: &[u8] = _letpattern5.1;
                                                                  let no_dup: bool =
                                                                      crate::cbordetver::cbor_det_serialize_map_insert(
                                                                          out_,
                                                                          size0,
                                                                          size1·
                                                                      );
                                                                  if no_dup
                                                                  {
                                                                      let
                                                                      __anf00:
                                                                      map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_CBOR_Pulse_Raw_Type_cbor_raw
                                                                      =
                                                                          (&pc)[0usize];
                                                                      let
                                                                      mut
                                                                      pj2:
                                                                      [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry;
                                                                      1]
                                                                      =
                                                                          [__anf00.cddl_map_iterator_contents;
                                                                              1usize];
                                                                      let mut pres2: [bool; 1] =
                                                                          [true; 1usize];
                                                                      let
                                                                      j1:
                                                                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                                                      =
                                                                          (&pj2)[0usize];
                                                                      let test0: bool =
                                                                          crate::cbordetver::cbor_det_map_iterator_is_empty(
                                                                              j1
                                                                          );
                                                                      let res3: bool =
                                                                          (&pres2)[0usize];
                                                                      let mut cond1: bool =
                                                                          res3 && ! test0;
                                                                      while
                                                                      cond1
                                                                      {
                                                                          let
                                                                          elt:
                                                                          crate::cbordetveraux::cbor_map_entry
                                                                          =
                                                                              crate::cbordetver::cbor_det_map_iterator_next(
                                                                                  &mut pj2
                                                                              );
                                                                          let
                                                                          elt_key:
                                                                          crate::cbordetveraux::cbor_raw
                                                                          =
                                                                              crate::cbordetver::cbor_det_map_entry_key(
                                                                                  elt
                                                                              );
                                                                          let test_key: bool =
                                                                              (__anf00.cddl_map_iterator_impl_validate1)(
                                                                                  elt_key
                                                                              );
                                                                          if ! ! test_key
                                                                          {
                                                                              let test_ex: bool =
                                                                                  (__anf00.cddl_map_iterator_impl_validate_ex)(
                                                                                      elt
                                                                                  );
                                                                              if ! test_ex
                                                                              {
                                                                                  let
                                                                                  elt_value:
                                                                                  crate::cbordetveraux::cbor_raw
                                                                                  =
                                                                                      crate::cbordetver::cbor_det_map_entry_value(
                                                                                          elt
                                                                                      );
                                                                                  let
                                                                                  test_value: bool
                                                                                  =
                                                                                      (__anf00.cddl_map_iterator_impl_validate2)(
                                                                                          elt_value
                                                                                      );
                                                                                  (&mut pres2)[0usize] =
                                                                                      ! test_value
                                                                              }
                                                                          };
                                                                          let
                                                                          j10:
                                                                          crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                                                          =
                                                                              (&pj2)[0usize];
                                                                          let test1: bool =
                                                                              crate::cbordetver::cbor_det_map_iterator_is_empty(
                                                                                  j10
                                                                              );
                                                                          let res30: bool =
                                                                              (&pres2)[0usize];
                                                                          cond1 = res30 && ! test1
                                                                      };
                                                                      let __anf10: bool =
                                                                          (&pres2)[0usize];
                                                                      (&mut pem)[0usize] = __anf10;
                                                                      (&mut psize)[0usize] = size2·;
                                                                      (&mut pcount)[0usize] =
                                                                          count·
                                                                  }
                                                                  else
                                                                  { (&mut pres)[0usize] = false }
                                                              }
                                                          },
                                                        _ => panic!("Incomplete pattern matching")
                                                    }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          }
                                      }
                                  }
                              };
                              let __anf10: bool = (&pres)[0usize];
                              let __anf00: bool = (&pem)[0usize];
                              cond0 = __anf10 && ! __anf00
                          };
                          (&pres)[0usize]
                      },
                    _ => panic!("Incomplete pattern matching")
                }
            }
            else
            { false }
        };
    if res
    {
        let size: usize = (&psize)[0usize];
        let count: u64 = (&pcount)[0usize];
        crate::cbordetver::cbor_det_serialize_map(count, out, size)
    }
    else
    { 0usize }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_cose_key_okp···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (cose_key_okp <'a>, &'a [u8]) }
}

pub fn validate_and_parse_cose_key_okp <'a>(s: &'a [u8]) ->
    option__·COSE_Format_cose_key_okp···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·COSE_Format_cose_key_okp···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_cose_key_okp(rl);
              if test
              {
                  let x: cose_key_okp = parse_cose_key_okp(rl);
                  option__·COSE_Format_cose_key_okp···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_cose_key_okp···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_cose_key(c: crate::cbordetveraux::cbor_raw) -> bool
{ validate_cose_key_okp(c) }

pub type cose_key_ugly <'a> = cose_key_okp <'a>;

pub type cose_key <'a> = cose_key_okp <'a>;

pub fn cose_key_right <'a>(x1: cose_key_okp <'a>) -> cose_key_okp <'a> { x1 }

pub fn cose_key_left <'a>(x4: cose_key_okp <'a>) -> cose_key_okp <'a> { x4 }

/**
Parser for cose_key
*/
pub fn
parse_cose_key
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    cose_key_okp
    <'a>
{ parse_cose_key_okp(c) }

/**
Serializer for cose_key
*/
pub fn
serialize_cose_key(c: cose_key_okp, out: &mut [u8]) ->
    usize
{ serialize_cose_key_okp(c, out) }

pub fn validate_and_parse_cose_key <'a>(s: &'a [u8]) ->
    option__·COSE_Format_cose_key_okp···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·COSE_Format_cose_key_okp···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_cose_key(rl);
              if test
              {
                  let x: cose_key_okp = parse_cose_key(rl);
                  option__·COSE_Format_cose_key_okp···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_cose_key_okp···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_header_map···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (header_map <'a>, &'a [u8]) }
}

pub fn validate_and_parse_header_map <'a>(s: &'a [u8]) ->
    option__·COSE_Format_header_map···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·COSE_Format_header_map···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_header_map(rl);
              if test
              {
                  let x: header_map = parse_header_map(rl);
                  option__·COSE_Format_header_map···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_header_map···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn is_empty_iterate_array_aux_env34_type_1(
    i:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
) ->
    bool
{ crate::cbordetver::cbor_det_array_iterator_is_empty(i.cddl_array_iterator_contents) }

pub fn next_iterate_array_aux_env34_type_1 <'a>(
    pi:
    &'a mut
    [array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
    <'a>]
) ->
    evercddl_label
    <'a>
{
    let
    i:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
    =
        pi[0usize];
    let len0: u64 =
        crate::cbordetver::cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
    let mut pj: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [i.cddl_array_iterator_contents; 1usize];
    let discarded: bool = (i.cddl_array_iterator_impl_validate)(&mut pj);
    crate::lowstar::ignore::ignore::<bool>(discarded);
    let ji: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pj)[0usize];
    let len1: u64 = crate::cbordetver::cbor_det_array_iterator_length(ji);
    let
    j:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
    =
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_evercddl_label
        {
            cddl_array_iterator_contents: ji,
            cddl_array_iterator_impl_validate: i.cddl_array_iterator_impl_validate,
            cddl_array_iterator_impl_parse: i.cddl_array_iterator_impl_parse
        };
    pi[0usize] = j;
    let tri: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(
            i.cddl_array_iterator_contents,
            len0.wrapping_sub(len1)
        );
    (i.cddl_array_iterator_impl_parse)(tri)
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_empty_or_serialized_map···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (empty_or_serialized_map <'a>, &'a [u8]) }
}

pub fn validate_and_parse_empty_or_serialized_map <'a>(s: &'a [u8]) ->
    option__·COSE_Format_empty_or_serialized_map···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·COSE_Format_empty_or_serialized_map···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_empty_or_serialized_map(rl);
              if test
              {
                  let x: empty_or_serialized_map = parse_empty_or_serialized_map(rl);
                  option__·COSE_Format_empty_or_serialized_map···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_empty_or_serialized_map···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_sig_structure(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let ty: u8 = crate::cbordetver::cbor_det_major_type(c);
    if ty == crate::cbordetveraux::cbor_major_type_array
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
            match v
            {
                crate::cbordetver::cbor_det_view::Array { _0: a } =>
                  crate::cbordetver::cbor_det_array_iterator_start(a),
                _ => panic!("Incomplete pattern matching")
            };
        let mut pi: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
            [i; 1usize];
        let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
            (&pi)[0usize];
        let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
        let test1: bool =
            if is_done
            { false }
            else
            {
                let c1: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
                let test: bool = mt == crate::cbordetveraux::cbor_major_type_text_string;
                let test1: bool =
                    if test
                    {
                        let v1: crate::cbordetver::cbor_det_view =
                            crate::cbordetver::cbor_det_destruct(c1);
                        let s: &[u8] =
                            match v1
                            {
                                crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                                _ => panic!("Incomplete pattern matching")
                            };
                        let __anf0: bool = crate::cbordetveraux::sizet_eq_u64(s.len(), 9u64);
                        if ! __anf0
                        { false }
                        else
                        {
                            let x: u8 = s[0usize];
                            let i·: usize = 1usize;
                            if x == 83u8
                            {
                                let x1: u8 = s[i·];
                                let i·1: usize = i·.wrapping_add(1usize);
                                if x1 == 105u8
                                {
                                    let x2: u8 = s[i·1];
                                    let i·2: usize = i·1.wrapping_add(1usize);
                                    if x2 == 103u8
                                    {
                                        let x3: u8 = s[i·2];
                                        let i·3: usize = i·2.wrapping_add(1usize);
                                        if x3 == 110u8
                                        {
                                            let x4: u8 = s[i·3];
                                            let i·4: usize = i·3.wrapping_add(1usize);
                                            if x4 == 97u8
                                            {
                                                let x5: u8 = s[i·4];
                                                let i·5: usize = i·4.wrapping_add(1usize);
                                                if x5 == 116u8
                                                {
                                                    let x6: u8 = s[i·5];
                                                    let i·6: usize = i·5.wrapping_add(1usize);
                                                    if x6 == 117u8
                                                    {
                                                        let x7: u8 = s[i·6];
                                                        let i·7: usize = i·6.wrapping_add(1usize);
                                                        if x7 == 114u8
                                                        {
                                                            let x8: u8 = s[i·7];
                                                            x8 == 101u8
                                                        }
                                                        else
                                                        { false }
                                                    }
                                                    else
                                                    { false }
                                                }
                                                else
                                                { false }
                                            }
                                            else
                                            { false }
                                        }
                                        else
                                        { false }
                                    }
                                    else
                                    { false }
                                }
                                else
                                { false }
                            }
                            else
                            { false }
                        }
                    }
                    else
                    { false };
                if test1
                { true }
                else
                {
                    let mt1: u8 = crate::cbordetver::cbor_det_major_type(c1);
                    let test2: bool = mt1 == crate::cbordetveraux::cbor_major_type_text_string;
                    if test2
                    {
                        let v1: crate::cbordetver::cbor_det_view =
                            crate::cbordetver::cbor_det_destruct(c1);
                        let s: &[u8] =
                            match v1
                            {
                                crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                                _ => panic!("Incomplete pattern matching")
                            };
                        let __anf0: bool = crate::cbordetveraux::sizet_eq_u64(s.len(), 10u64);
                        if ! __anf0
                        { false }
                        else
                        {
                            let x: u8 = s[0usize];
                            let i·: usize = 1usize;
                            if x == 83u8
                            {
                                let x1: u8 = s[i·];
                                let i·1: usize = i·.wrapping_add(1usize);
                                if x1 == 105u8
                                {
                                    let x2: u8 = s[i·1];
                                    let i·2: usize = i·1.wrapping_add(1usize);
                                    if x2 == 103u8
                                    {
                                        let x3: u8 = s[i·2];
                                        let i·3: usize = i·2.wrapping_add(1usize);
                                        if x3 == 110u8
                                        {
                                            let x4: u8 = s[i·3];
                                            let i·4: usize = i·3.wrapping_add(1usize);
                                            if x4 == 97u8
                                            {
                                                let x5: u8 = s[i·4];
                                                let i·5: usize = i·4.wrapping_add(1usize);
                                                if x5 == 116u8
                                                {
                                                    let x6: u8 = s[i·5];
                                                    let i·6: usize = i·5.wrapping_add(1usize);
                                                    if x6 == 117u8
                                                    {
                                                        let x7: u8 = s[i·6];
                                                        let i·7: usize = i·6.wrapping_add(1usize);
                                                        if x7 == 114u8
                                                        {
                                                            let x8: u8 = s[i·7];
                                                            let i·8: usize =
                                                                i·7.wrapping_add(1usize);
                                                            if x8 == 101u8
                                                            {
                                                                let x9: u8 = s[i·8];
                                                                x9 == 49u8
                                                            }
                                                            else
                                                            { false }
                                                        }
                                                        else
                                                        { false }
                                                    }
                                                    else
                                                    { false }
                                                }
                                                else
                                                { false }
                                            }
                                            else
                                            { false }
                                        }
                                        else
                                        { false }
                                    }
                                    else
                                    { false }
                                }
                                else
                                { false }
                            }
                            else
                            { false }
                        }
                    }
                    else
                    { false }
                }
            };
        let b_success: bool =
            if test1
            {
                let i2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0usize];
                let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
                let test11: bool =
                    if is_done1
                    { false }
                    else
                    {
                        let c1: crate::cbordetveraux::cbor_raw =
                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                        validate_empty_or_serialized_map(c1)
                    };
                if test11
                {
                    let i3: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                        (&pi)[0usize];
                    let i4: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                        (&pi)[0usize];
                    let is_done2: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i4);
                    let test12: bool =
                        if is_done2
                        { false }
                        else
                        {
                            let c1: crate::cbordetveraux::cbor_raw =
                                crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                            validate_empty_or_serialized_map(c1)
                        };
                    let test13: bool =
                        if test12
                        {
                            let
                            i5:
                            crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                            =
                                (&pi)[0usize];
                            let is_done3: bool =
                                crate::cbordetver::cbor_det_array_iterator_is_empty(i5);
                            let test13: bool =
                                if is_done3
                                { false }
                                else
                                {
                                    let c1: crate::cbordetveraux::cbor_raw =
                                        crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                    validate_bstr(c1)
                                };
                            if test13
                            {
                                let
                                i6:
                                crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                =
                                    (&pi)[0usize];
                                let is_done4: bool =
                                    crate::cbordetver::cbor_det_array_iterator_is_empty(i6);
                                if is_done4
                                { false }
                                else
                                {
                                    let c1: crate::cbordetveraux::cbor_raw =
                                        crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                    validate_bstr(c1)
                                }
                            }
                            else
                            { false }
                        }
                        else
                        { false };
                    if test13
                    { true }
                    else
                    {
                        (&mut pi)[0usize] = i3;
                        let
                        i5: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                        =
                            (&pi)[0usize];
                        let is_done3: bool =
                            crate::cbordetver::cbor_det_array_iterator_is_empty(i5);
                        let test14: bool =
                            if is_done3
                            { false }
                            else
                            {
                                let c1: crate::cbordetveraux::cbor_raw =
                                    crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                validate_bstr(c1)
                            };
                        if test14
                        {
                            let
                            i6:
                            crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                            =
                                (&pi)[0usize];
                            let is_done4: bool =
                                crate::cbordetver::cbor_det_array_iterator_is_empty(i6);
                            if is_done4
                            { false }
                            else
                            {
                                let c1: crate::cbordetveraux::cbor_raw =
                                    crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                validate_bstr(c1)
                            }
                        }
                        else
                        { false }
                    }
                }
                else
                { false }
            }
            else
            { false };
        if b_success
        {
            let i·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pi)[0usize];
            crate::cbordetver::cbor_det_array_iterator_is_empty(i·)
        }
        else
        { false }
    }
    else
    { false }
}

pub fn sig_structure_right <'a>(
    x3:
    (either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t_tags,
    (empty_or_serialized_map
    <'a>,
    either__·COSE_Format_empty_or_serialized_map····Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t··_·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·
    <'a>))
) ->
    sig_structure
    <'a>
{ match x3 { (x4,(x5,x6)) => sig_structure { context: x4, body_protected: x5, _x0: x6 } } }

/**
Parser for sig_structure
*/
pub fn
parse_sig_structure
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    sig_structure
    <'a>
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let ar: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        match v
        {
            crate::cbordetver::cbor_det_view::Array { _0: a } =>
              crate::cbordetver::cbor_det_array_iterator_start(a),
            _ => panic!("Incomplete pattern matching")
        };
    let rlen0: u64 = crate::cbordetver::cbor_det_array_iterator_length(ar);
    let mut pc: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [ar; 1usize];
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0usize];
    let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i);
    let discarded: bool =
        if is_done
        { false }
        else
        {
            let c1: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
            let test: bool = mt == crate::cbordetveraux::cbor_major_type_text_string;
            let test1: bool =
                if test
                {
                    let v1: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(c1);
                    let s: &[u8] =
                        match v1
                        {
                            crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                            _ => panic!("Incomplete pattern matching")
                        };
                    let __anf0: bool = crate::cbordetveraux::sizet_eq_u64(s.len(), 9u64);
                    if ! __anf0
                    { false }
                    else
                    {
                        let x: u8 = s[0usize];
                        let i·: usize = 1usize;
                        if x == 83u8
                        {
                            let x1: u8 = s[i·];
                            let i·1: usize = i·.wrapping_add(1usize);
                            if x1 == 105u8
                            {
                                let x2: u8 = s[i·1];
                                let i·2: usize = i·1.wrapping_add(1usize);
                                if x2 == 103u8
                                {
                                    let x3: u8 = s[i·2];
                                    let i·3: usize = i·2.wrapping_add(1usize);
                                    if x3 == 110u8
                                    {
                                        let x4: u8 = s[i·3];
                                        let i·4: usize = i·3.wrapping_add(1usize);
                                        if x4 == 97u8
                                        {
                                            let x5: u8 = s[i·4];
                                            let i·5: usize = i·4.wrapping_add(1usize);
                                            if x5 == 116u8
                                            {
                                                let x6: u8 = s[i·5];
                                                let i·6: usize = i·5.wrapping_add(1usize);
                                                if x6 == 117u8
                                                {
                                                    let x7: u8 = s[i·6];
                                                    let i·7: usize = i·6.wrapping_add(1usize);
                                                    if x7 == 114u8
                                                    {
                                                        let x8: u8 = s[i·7];
                                                        x8 == 101u8
                                                    }
                                                    else
                                                    { false }
                                                }
                                                else
                                                { false }
                                            }
                                            else
                                            { false }
                                        }
                                        else
                                        { false }
                                    }
                                    else
                                    { false }
                                }
                                else
                                { false }
                            }
                            else
                            { false }
                        }
                        else
                        { false }
                    }
                }
                else
                { false };
            if test1
            { true }
            else
            {
                let mt1: u8 = crate::cbordetver::cbor_det_major_type(c1);
                let test2: bool = mt1 == crate::cbordetveraux::cbor_major_type_text_string;
                if test2
                {
                    let v1: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(c1);
                    let s: &[u8] =
                        match v1
                        {
                            crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                            _ => panic!("Incomplete pattern matching")
                        };
                    let __anf0: bool = crate::cbordetveraux::sizet_eq_u64(s.len(), 10u64);
                    if ! __anf0
                    { false }
                    else
                    {
                        let x: u8 = s[0usize];
                        let i·: usize = 1usize;
                        if x == 83u8
                        {
                            let x1: u8 = s[i·];
                            let i·1: usize = i·.wrapping_add(1usize);
                            if x1 == 105u8
                            {
                                let x2: u8 = s[i·1];
                                let i·2: usize = i·1.wrapping_add(1usize);
                                if x2 == 103u8
                                {
                                    let x3: u8 = s[i·2];
                                    let i·3: usize = i·2.wrapping_add(1usize);
                                    if x3 == 110u8
                                    {
                                        let x4: u8 = s[i·3];
                                        let i·4: usize = i·3.wrapping_add(1usize);
                                        if x4 == 97u8
                                        {
                                            let x5: u8 = s[i·4];
                                            let i·5: usize = i·4.wrapping_add(1usize);
                                            if x5 == 116u8
                                            {
                                                let x6: u8 = s[i·5];
                                                let i·6: usize = i·5.wrapping_add(1usize);
                                                if x6 == 117u8
                                                {
                                                    let x7: u8 = s[i·6];
                                                    let i·7: usize = i·6.wrapping_add(1usize);
                                                    if x7 == 114u8
                                                    {
                                                        let x8: u8 = s[i·7];
                                                        let i·8: usize = i·7.wrapping_add(1usize);
                                                        if x8 == 101u8
                                                        {
                                                            let x9: u8 = s[i·8];
                                                            x9 == 49u8
                                                        }
                                                        else
                                                        { false }
                                                    }
                                                    else
                                                    { false }
                                                }
                                                else
                                                { false }
                                            }
                                            else
                                            { false }
                                        }
                                        else
                                        { false }
                                    }
                                    else
                                    { false }
                                }
                                else
                                { false }
                            }
                            else
                            { false }
                        }
                        else
                        { false }
                    }
                }
                else
                { false }
            }
        };
    crate::lowstar::ignore::ignore::<bool>(discarded);
    let c1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0usize];
    let rlen1: u64 = crate::cbordetver::cbor_det_array_iterator_length(c1);
    let c0·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(ar, rlen0.wrapping_sub(rlen1));
    let mut pc1: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·; 1usize];
    let x: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc1);
    let mt: u8 = crate::cbordetver::cbor_det_major_type(x);
    let test: bool = mt == crate::cbordetveraux::cbor_major_type_text_string;
    let test1: bool =
        if test
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(x);
            let s: &[u8] =
                match v1
                {
                    crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let __anf0: bool = crate::cbordetveraux::sizet_eq_u64(s.len(), 9u64);
            if ! __anf0
            { false }
            else
            {
                let x1: u8 = s[0usize];
                let i·: usize = 1usize;
                if x1 == 83u8
                {
                    let x2: u8 = s[i·];
                    let i·1: usize = i·.wrapping_add(1usize);
                    if x2 == 105u8
                    {
                        let x3: u8 = s[i·1];
                        let i·2: usize = i·1.wrapping_add(1usize);
                        if x3 == 103u8
                        {
                            let x4: u8 = s[i·2];
                            let i·3: usize = i·2.wrapping_add(1usize);
                            if x4 == 110u8
                            {
                                let x5: u8 = s[i·3];
                                let i·4: usize = i·3.wrapping_add(1usize);
                                if x5 == 97u8
                                {
                                    let x6: u8 = s[i·4];
                                    let i·5: usize = i·4.wrapping_add(1usize);
                                    if x6 == 116u8
                                    {
                                        let x7: u8 = s[i·5];
                                        let i·6: usize = i·5.wrapping_add(1usize);
                                        if x7 == 117u8
                                        {
                                            let x8: u8 = s[i·6];
                                            let i·7: usize = i·6.wrapping_add(1usize);
                                            if x8 == 114u8
                                            {
                                                let x9: u8 = s[i·7];
                                                x9 == 101u8
                                            }
                                            else
                                            { false }
                                        }
                                        else
                                        { false }
                                    }
                                    else
                                    { false }
                                }
                                else
                                { false }
                            }
                            else
                            { false }
                        }
                        else
                        { false }
                    }
                    else
                    { false }
                }
                else
                { false }
            }
        }
        else
        { false };
    let w1: either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t_tags =
        if test1
        { either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t_tags::Inl }
        else
        { either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t_tags::Inr };
    let rlen01: u64 = crate::cbordetver::cbor_det_array_iterator_length(c1);
    let mut pc2: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c1; 1usize];
    let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc2)[0usize];
    let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
    let discarded1: bool =
        if is_done1
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc2);
            validate_empty_or_serialized_map(c2)
        };
    crate::lowstar::ignore::ignore::<bool>(discarded1);
    let c11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        (&pc2)[0usize];
    let rlen11: u64 = crate::cbordetver::cbor_det_array_iterator_length(c11);
    let c0·1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c1, rlen01.wrapping_sub(rlen11));
    let mut pc3: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·1; 1usize];
    let x1: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc3);
    let w11: empty_or_serialized_map = parse_empty_or_serialized_map(x1);
    let mut pc4: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c11; 1usize];
    let i2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc4)[0usize];
    let is_done2: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
    let test11: bool =
        if is_done2
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc4);
            validate_empty_or_serialized_map(c2)
        };
    let test12: bool =
        if test11
        {
            let i3: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc4)[0usize];
            let is_done3: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i3);
            let test12: bool =
                if is_done3
                { false }
                else
                {
                    let c2: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_array_iterator_next(&mut pc4);
                    validate_bstr(c2)
                };
            if test12
            {
                let i4: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pc4)[0usize];
                let is_done4: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i4);
                if is_done4
                { false }
                else
                {
                    let c2: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_array_iterator_next(&mut pc4);
                    validate_bstr(c2)
                }
            }
            else
            { false }
        }
        else
        { false };
    let
    w2:
    either__·COSE_Format_empty_or_serialized_map····Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t··_·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·
    =
        if test12
        {
            let rlen02: u64 = crate::cbordetver::cbor_det_array_iterator_length(c11);
            let
            mut pc5: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
            =
                [c11; 1usize];
            let i3: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc5)[0usize];
            let is_done3: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i3);
            let discarded2: bool =
                if is_done3
                { false }
                else
                {
                    let c2: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_array_iterator_next(&mut pc5);
                    validate_empty_or_serialized_map(c2)
                };
            crate::lowstar::ignore::ignore::<bool>(discarded2);
            let c12: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc5)[0usize];
            let rlen12: u64 = crate::cbordetver::cbor_det_array_iterator_length(c12);
            let c0·2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_truncate(
                    c11,
                    rlen02.wrapping_sub(rlen12)
                );
            let
            mut pc6: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
            =
                [c0·2; 1usize];
            let x2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc6);
            let w12: empty_or_serialized_map = parse_empty_or_serialized_map(x2);
            let rlen03: u64 = crate::cbordetver::cbor_det_array_iterator_length(c12);
            let
            mut pc7: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
            =
                [c12; 1usize];
            let i4: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc7)[0usize];
            let is_done4: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i4);
            let discarded3: bool =
                if is_done4
                { false }
                else
                {
                    let c2: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_array_iterator_next(&mut pc7);
                    validate_bstr(c2)
                };
            crate::lowstar::ignore::ignore::<bool>(discarded3);
            let c13: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc7)[0usize];
            let rlen13: u64 = crate::cbordetver::cbor_det_array_iterator_length(c13);
            let c0·3: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_truncate(
                    c12,
                    rlen03.wrapping_sub(rlen13)
                );
            let
            mut pc8: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
            =
                [c0·3; 1usize];
            let x3: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc8);
            let w13: &[u8] = parse_bstr(x3);
            let
            mut pc9: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
            =
                [c13; 1usize];
            let x4: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc9);
            let w2: &[u8] = parse_bstr(x4);
            let w21: (&[u8], &[u8]) = (w13,w2);
            let w14: (empty_or_serialized_map, (&[u8], &[u8])) = (w12,w21);
            either__·COSE_Format_empty_or_serialized_map····Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t··_·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::Inl
            { v: w14 }
        }
        else
        {
            let rlen02: u64 = crate::cbordetver::cbor_det_array_iterator_length(c11);
            let
            mut pc5: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
            =
                [c11; 1usize];
            let i3: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc5)[0usize];
            let is_done3: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i3);
            let discarded2: bool =
                if is_done3
                { false }
                else
                {
                    let c2: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_array_iterator_next(&mut pc5);
                    validate_bstr(c2)
                };
            crate::lowstar::ignore::ignore::<bool>(discarded2);
            let c12: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc5)[0usize];
            let rlen12: u64 = crate::cbordetver::cbor_det_array_iterator_length(c12);
            let c0·2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_truncate(
                    c11,
                    rlen02.wrapping_sub(rlen12)
                );
            let
            mut pc6: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
            =
                [c0·2; 1usize];
            let x2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc6);
            let w12: &[u8] = parse_bstr(x2);
            let
            mut pc7: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
            =
                [c12; 1usize];
            let x3: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc7);
            let w2: &[u8] = parse_bstr(x3);
            let w21: (&[u8], &[u8]) = (w12,w2);
            either__·COSE_Format_empty_or_serialized_map····Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t··_·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·::Inr
            { v: w21 }
        };
    let
    w21:
    (empty_or_serialized_map,
    either__·COSE_Format_empty_or_serialized_map····Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t··_·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·)
    =
        (w11,w2);
    let
    res1:
    (either__COSE_Format_evercddl_int_Pulse_Lib_Slice_slice·uint8_t_tags,
    (empty_or_serialized_map,
    either__·COSE_Format_empty_or_serialized_map····Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t··_·Pulse_Lib_Slice_slice·uint8_t···Pulse_Lib_Slice_slice·uint8_t·))
    =
        (w1,w21);
    sig_structure_right(res1)
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_sig_structure···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (sig_structure <'a>, &'a [u8]) }
}

pub fn validate_and_parse_sig_structure <'a>(s: &'a [u8]) ->
    option__·COSE_Format_sig_structure···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·COSE_Format_sig_structure···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_sig_structure(rl);
              if test
              {
                  let x: sig_structure = parse_sig_structure(rl);
                  option__·COSE_Format_sig_structure···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_sig_structure···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_and_parse_cose_sign1 <'a>(s: &'a [u8]) ->
    option__·COSE_Format_cose_sign1···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·COSE_Format_cose_sign1···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_cose_sign1(rl);
              if test
              {
                  let x: cose_sign1 = parse_cose_sign1(rl);
                  option__·COSE_Format_cose_sign1···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_cose_sign1···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_cose_signature(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let ty: u8 = crate::cbordetver::cbor_det_major_type(c);
    if ty == crate::cbordetveraux::cbor_major_type_array
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
            match v
            {
                crate::cbordetver::cbor_det_view::Array { _0: a } =>
                  crate::cbordetver::cbor_det_array_iterator_start(a),
                _ => panic!("Incomplete pattern matching")
            };
        let mut pi: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
            [i; 1usize];
        let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
            (&pi)[0usize];
        let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
        let test1: bool =
            if is_done
            { false }
            else
            {
                let c1: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                validate_empty_or_serialized_map(c1)
            };
        let test11: bool =
            if test1
            {
                let i2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0usize];
                let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
                if is_done1
                { false }
                else
                {
                    let c1: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                    validate_header_map(c1)
                }
            }
            else
            { false };
        let b_success: bool =
            if test11
            {
                let i2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0usize];
                let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
                if is_done1
                { false }
                else
                {
                    let c1: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                    validate_bstr(c1)
                }
            }
            else
            { false };
        if b_success
        {
            let i·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pi)[0usize];
            crate::cbordetver::cbor_det_array_iterator_is_empty(i·)
        }
        else
        { false }
    }
    else
    { false }
}

#[derive(PartialEq, Clone, Copy)]
pub struct cose_signature <'a>
{
    pub protected: empty_or_serialized_map <'a>,
    pub unprotected: header_map <'a>,
    pub signature: &'a [u8]
}

pub fn cose_signature_right <'a>(
    x3: ((empty_or_serialized_map <'a>, header_map <'a>), &'a [u8])
) ->
    cose_signature
    <'a>
{
    match x3 { ((x4,x5),x6) => cose_signature { protected: x4, unprotected: x5, signature: x6 } }
}

pub fn cose_signature_left <'a>(x8: cose_signature <'a>) ->
    ((empty_or_serialized_map <'a>, header_map <'a>), &'a [u8])
{ ((x8.protected,x8.unprotected),x8.signature) }

/**
Parser for cose_signature
*/
pub fn
parse_cose_signature
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    cose_signature
    <'a>
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let ar: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        match v
        {
            crate::cbordetver::cbor_det_view::Array { _0: a } =>
              crate::cbordetver::cbor_det_array_iterator_start(a),
            _ => panic!("Incomplete pattern matching")
        };
    let rlen0: u64 = crate::cbordetver::cbor_det_array_iterator_length(ar);
    let mut pc: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [ar; 1usize];
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0usize];
    let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i);
    let test1: bool =
        if is_done
        { false }
        else
        {
            let c1: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
            validate_empty_or_serialized_map(c1)
        };
    let discarded: bool =
        if test1
        {
            let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc)[0usize];
            let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
            if is_done1
            { false }
            else
            {
                let c1: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
                validate_header_map(c1)
            }
        }
        else
        { false };
    crate::lowstar::ignore::ignore::<bool>(discarded);
    let c1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0usize];
    let rlen1: u64 = crate::cbordetver::cbor_det_array_iterator_length(c1);
    let c0·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(ar, rlen0.wrapping_sub(rlen1));
    let rlen01: u64 = crate::cbordetver::cbor_det_array_iterator_length(c0·);
    let mut pc1: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·; 1usize];
    let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc1)[0usize];
    let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
    let discarded1: bool =
        if is_done1
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc1);
            validate_empty_or_serialized_map(c2)
        };
    crate::lowstar::ignore::ignore::<bool>(discarded1);
    let c11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        (&pc1)[0usize];
    let rlen11: u64 = crate::cbordetver::cbor_det_array_iterator_length(c11);
    let c0·1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c0·, rlen01.wrapping_sub(rlen11));
    let mut pc2: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·1; 1usize];
    let x: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc2);
    let w1: empty_or_serialized_map = parse_empty_or_serialized_map(x);
    let mut pc3: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c11; 1usize];
    let x1: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc3);
    let w2: header_map = parse_header_map(x1);
    let w11: (empty_or_serialized_map, header_map) = (w1,w2);
    let mut pc4: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c1; 1usize];
    let x2: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc4);
    let w21: &[u8] = parse_bstr(x2);
    let res1: ((empty_or_serialized_map, header_map), &[u8]) = (w11,w21);
    cose_signature_right(res1)
}

/**
Serializer for cose_signature
*/
pub fn
serialize_cose_signature(c: cose_signature, out: &mut [u8]) ->
    usize
{
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let _letpattern: ((empty_or_serialized_map, header_map), &[u8]) = cose_signature_left(c);
    let res: bool =
        {
            let c1: (empty_or_serialized_map, header_map) = _letpattern.0;
            let c2: &[u8] = _letpattern.1;
            let res1: bool =
                {
                    let c11: empty_or_serialized_map = c1.0;
                    let c21: header_map = c1.1;
                    let count: u64 = (&pcount)[0usize];
                    let res1: bool =
                        if count < 18446744073709551615u64
                        {
                            let size: usize = (&psize)[0usize];
                            let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                            let _out0: &[u8] = _letpattern1.0;
                            let out1: &mut [u8] = _letpattern1.1;
                            let size1: usize = serialize_empty_or_serialized_map(c11, out1);
                            if size1 == 0usize
                            { false }
                            else
                            {
                                (&mut pcount)[0usize] = count.wrapping_add(1u64);
                                (&mut psize)[0usize] = size.wrapping_add(size1);
                                true
                            }
                        }
                        else
                        { false };
                    if res1
                    {
                        let count1: u64 = (&pcount)[0usize];
                        if count1 < 18446744073709551615u64
                        {
                            let size: usize = (&psize)[0usize];
                            let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                            let _out0: &[u8] = _letpattern1.0;
                            let out1: &mut [u8] = _letpattern1.1;
                            let size1: usize = serialize_header_map(c21, out1);
                            if size1 == 0usize
                            { false }
                            else
                            {
                                (&mut pcount)[0usize] = count1.wrapping_add(1u64);
                                (&mut psize)[0usize] = size.wrapping_add(size1);
                                true
                            }
                        }
                        else
                        { false }
                    }
                    else
                    { false }
                };
            if res1
            {
                let count: u64 = (&pcount)[0usize];
                if count < 18446744073709551615u64
                {
                    let size: usize = (&psize)[0usize];
                    let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                    let _out0: &[u8] = _letpattern1.0;
                    let out1: &mut [u8] = _letpattern1.1;
                    let size1: usize = serialize_bstr(c2, out1);
                    if size1 == 0usize
                    { false }
                    else
                    {
                        (&mut pcount)[0usize] = count.wrapping_add(1u64);
                        (&mut psize)[0usize] = size.wrapping_add(size1);
                        true
                    }
                }
                else
                { false }
            }
            else
            { false }
        };
    if res
    {
        let size: usize = (&psize)[0usize];
        let count: u64 = (&pcount)[0usize];
        crate::cbordetver::cbor_det_serialize_array(count, out, size)
    }
    else
    { 0usize }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_cose_signature···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (cose_signature <'a>, &'a [u8]) }
}

pub fn validate_and_parse_cose_signature <'a>(s: &'a [u8]) ->
    option__·COSE_Format_cose_signature···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·COSE_Format_cose_signature···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_cose_signature(rl);
              if test
              {
                  let x: cose_signature = parse_cose_signature(rl);
                  option__·COSE_Format_cose_signature···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_cose_signature···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn aux_env41_validate_1(
    pi: &mut [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw]
) ->
    bool
{
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = pi[0usize];
    let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i);
    if is_done
    { false }
    else
    {
        let c: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_array_iterator_next(pi);
        validate_cose_signature(c)
    }
}

pub type aux_env41_type_1_ugly <'a> = cose_signature <'a>;

pub type aux_env41_type_1 <'a> = cose_signature <'a>;

pub fn aux_env41_type_1_right <'a>(x1: cose_signature <'a>) -> cose_signature <'a> { x1 }

pub fn aux_env41_type_1_left <'a>(x4: cose_signature <'a>) -> cose_signature <'a> { x4 }

/**
Parser for aux_env41_type_1
*/
pub fn
aux_env41_parse_1
<'a>(c: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>) ->
    cose_signature
    <'a>
{
    let mut pc: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c; 1usize];
    let x: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
    parse_cose_signature(x)
}

/**
Serializer for aux_env41_type_1
*/
pub fn
aux_env41_serialize_1(
    c: cose_signature,
    out: &mut [u8],
    out_count: &mut [u64],
    out_size: &mut [usize]
) ->
    bool
{
    let count: u64 = out_count[0usize];
    if count < 18446744073709551615u64
    {
        let size: usize = out_size[0usize];
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
        let _out0: &[u8] = _letpattern.0;
        let out1: &mut [u8] = _letpattern.1;
        let size1: usize = serialize_cose_signature(c, out1);
        if size1 == 0usize
        { false }
        else
        {
            out_count[0usize] = count.wrapping_add(1u64);
            out_size[0usize] = size.wrapping_add(size1);
            true
        }
    }
    else
    { false }
}

pub fn validate_cose_sign(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let ty: u8 = crate::cbordetver::cbor_det_major_type(c);
    if ty == crate::cbordetveraux::cbor_major_type_array
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
            match v
            {
                crate::cbordetver::cbor_det_view::Array { _0: a } =>
                  crate::cbordetver::cbor_det_array_iterator_start(a),
                _ => panic!("Incomplete pattern matching")
            };
        let mut pi: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
            [i; 1usize];
        let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
            (&pi)[0usize];
        let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
        let test1: bool =
            if is_done
            { false }
            else
            {
                let c1: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                validate_empty_or_serialized_map(c1)
            };
        let test11: bool =
            if test1
            {
                let i2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0usize];
                let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
                if is_done1
                { false }
                else
                {
                    let c1: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                    validate_header_map(c1)
                }
            }
            else
            { false };
        let b_success: bool =
            if test11
            {
                let i2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0usize];
                let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
                let test12: bool =
                    if is_done1
                    { false }
                    else
                    {
                        let c1: crate::cbordetveraux::cbor_raw =
                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                        let test: bool = validate_bstr(c1);
                        if test { true } else { validate_nil(c1) }
                    };
                if test12
                {
                    let i3: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                        (&pi)[0usize];
                    let is_done2: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i3);
                    if is_done2
                    { false }
                    else
                    {
                        let c1: crate::cbordetveraux::cbor_raw =
                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                        let ty1: u8 = crate::cbordetver::cbor_det_major_type(c1);
                        if ty1 == crate::cbordetveraux::cbor_major_type_array
                        {
                            let v1: crate::cbordetver::cbor_det_view =
                                crate::cbordetver::cbor_det_destruct(c1);
                            let
                            i4:
                            crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                            =
                                match v1
                                {
                                    crate::cbordetver::cbor_det_view::Array { _0: a } =>
                                      crate::cbordetver::cbor_det_array_iterator_start(a),
                                    _ => panic!("Incomplete pattern matching")
                                };
                            let
                            mut
                            pi1:
                            [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw;
                            1]
                            =
                                [i4; 1usize];
                            let
                            i5:
                            crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                            =
                                (&pi1)[0usize];
                            let is_done3: bool =
                                crate::cbordetver::cbor_det_array_iterator_is_empty(i5);
                            let test13: bool =
                                if is_done3
                                { false }
                                else
                                {
                                    let c2: crate::cbordetveraux::cbor_raw =
                                        crate::cbordetver::cbor_det_array_iterator_next(&mut pi1);
                                    validate_cose_signature(c2)
                                };
                            let b_success: bool =
                                if test13
                                {
                                    let mut pcont: [bool; 1] = [true; 1usize];
                                    while
                                    (&pcont)[0usize]
                                    {
                                        let
                                        i11:
                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                        =
                                            (&pi1)[0usize];
                                        let
                                        i6:
                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                        =
                                            (&pi1)[0usize];
                                        let is_done4: bool =
                                            crate::cbordetver::cbor_det_array_iterator_is_empty(i6);
                                        let cont: bool =
                                            if is_done4
                                            { false }
                                            else
                                            {
                                                let c2: crate::cbordetveraux::cbor_raw =
                                                    crate::cbordetver::cbor_det_array_iterator_next(
                                                        &mut pi1
                                                    );
                                                validate_cose_signature(c2)
                                            };
                                        if ! cont
                                        {
                                            (&mut pi1)[0usize] = i11;
                                            (&mut pcont)[0usize] = false
                                        }
                                    };
                                    true
                                }
                                else
                                { false };
                            if b_success
                            {
                                let
                                i·:
                                crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                =
                                    (&pi1)[0usize];
                                crate::cbordetver::cbor_det_array_iterator_is_empty(i·)
                            }
                            else
                            { false }
                        }
                        else
                        { false }
                    }
                }
                else
                { false }
            }
            else
            { false };
        if b_success
        {
            let i·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pi)[0usize];
            crate::cbordetver::cbor_det_array_iterator_is_empty(i·)
        }
        else
        { false }
    }
    else
    { false }
}

#[derive(PartialEq, Clone, Copy)]
pub struct
array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature
<'a>
{
    pub cddl_array_iterator_contents:
    crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>,
    pub cddl_array_iterator_impl_validate:
    fn (&mut [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw]) -> bool,
    pub cddl_array_iterator_impl_parse:
    for<'a1>
    fn
    (crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a1>)
    ->
    cose_signature
    <'a1>
}

#[derive(PartialEq, Clone, Copy)]
pub enum
either__Pulse_Lib_Slice_slice·COSE_Format_cose_signature_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature
<'a>
{
    Inl { v: &'a [cose_signature <'a>] },
    Inr
    {
        v:
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature
        <'a>
    }
}

#[derive(PartialEq, Clone, Copy)]
pub struct cose_sign <'a>
{
    pub protected: empty_or_serialized_map <'a>,
    pub unprotected: header_map <'a>,
    pub payload: either__Pulse_Lib_Slice_slice·uint8_t_·· <'a>,
    pub signatures:
    either__Pulse_Lib_Slice_slice·COSE_Format_cose_signature_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature
    <'a>
}

pub fn cose_sign_right <'a>(
    x4:
    ((empty_or_serialized_map <'a>, header_map <'a>),
    (either__Pulse_Lib_Slice_slice·uint8_t_··
    <'a>,
    either__Pulse_Lib_Slice_slice·COSE_Format_cose_signature_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature
    <'a>))
) ->
    cose_sign
    <'a>
{
    match x4
    {
        ((x5,x6),(x7,x8)) =>
          cose_sign { protected: x5, unprotected: x6, payload: x7, signatures: x8 }
    }
}

pub fn cose_sign_left <'a>(x10: cose_sign <'a>) ->
    ((empty_or_serialized_map <'a>, header_map <'a>),
    (either__Pulse_Lib_Slice_slice·uint8_t_··
    <'a>,
    either__Pulse_Lib_Slice_slice·COSE_Format_cose_signature_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature
    <'a>))
{ ((x10.protected,x10.unprotected),(x10.payload,x10.signatures)) }

/**
Parser for cose_sign
*/
pub fn
parse_cose_sign
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    cose_sign
    <'a>
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let ar: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        match v
        {
            crate::cbordetver::cbor_det_view::Array { _0: a } =>
              crate::cbordetver::cbor_det_array_iterator_start(a),
            _ => panic!("Incomplete pattern matching")
        };
    let rlen0: u64 = crate::cbordetver::cbor_det_array_iterator_length(ar);
    let mut pc: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [ar; 1usize];
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0usize];
    let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i);
    let test1: bool =
        if is_done
        { false }
        else
        {
            let c1: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
            validate_empty_or_serialized_map(c1)
        };
    let discarded: bool =
        if test1
        {
            let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc)[0usize];
            let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
            if is_done1
            { false }
            else
            {
                let c1: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
                validate_header_map(c1)
            }
        }
        else
        { false };
    crate::lowstar::ignore::ignore::<bool>(discarded);
    let c1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0usize];
    let rlen1: u64 = crate::cbordetver::cbor_det_array_iterator_length(c1);
    let c0·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(ar, rlen0.wrapping_sub(rlen1));
    let rlen01: u64 = crate::cbordetver::cbor_det_array_iterator_length(c0·);
    let mut pc1: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·; 1usize];
    let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc1)[0usize];
    let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
    let discarded1: bool =
        if is_done1
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc1);
            validate_empty_or_serialized_map(c2)
        };
    crate::lowstar::ignore::ignore::<bool>(discarded1);
    let c11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        (&pc1)[0usize];
    let rlen11: u64 = crate::cbordetver::cbor_det_array_iterator_length(c11);
    let c0·1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c0·, rlen01.wrapping_sub(rlen11));
    let mut pc2: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·1; 1usize];
    let x: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc2);
    let w1: empty_or_serialized_map = parse_empty_or_serialized_map(x);
    let mut pc3: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c11; 1usize];
    let x1: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc3);
    let w2: header_map = parse_header_map(x1);
    let w11: (empty_or_serialized_map, header_map) = (w1,w2);
    let rlen02: u64 = crate::cbordetver::cbor_det_array_iterator_length(c1);
    let mut pc4: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c1; 1usize];
    let i2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc4)[0usize];
    let is_done2: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
    let discarded2: bool =
        if is_done2
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc4);
            let test: bool = validate_bstr(c2);
            if test { true } else { validate_nil(c2) }
        };
    crate::lowstar::ignore::ignore::<bool>(discarded2);
    let c12: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        (&pc4)[0usize];
    let rlen12: u64 = crate::cbordetver::cbor_det_array_iterator_length(c12);
    let c0·2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c1, rlen02.wrapping_sub(rlen12));
    let mut pc5: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·2; 1usize];
    let x2: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc5);
    let test: bool = validate_bstr(x2);
    let w12: either__Pulse_Lib_Slice_slice·uint8_t_·· =
        if test
        {
            let res: &[u8] = parse_bstr(x2);
            either__Pulse_Lib_Slice_slice·uint8_t_··::Inl { v: res }
        }
        else
        {
            parse_nil(x2);
            either__Pulse_Lib_Slice_slice·uint8_t_··::Inr
        };
    let mut pc6: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c12; 1usize];
    let x3: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc6);
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(x3);
    let ar1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        match v1
        {
            crate::cbordetver::cbor_det_view::Array { _0: a } =>
              crate::cbordetver::cbor_det_array_iterator_start(a),
            _ => panic!("Incomplete pattern matching")
        };
    let
    i3:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature
    =
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature
        {
            cddl_array_iterator_contents: ar1,
            cddl_array_iterator_impl_validate:
            aux_env41_validate_1
            as
            fn
            (&mut [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw])
            ->
            bool,
            cddl_array_iterator_impl_parse: aux_env41_parse_1
        };
    let
    w21:
    either__Pulse_Lib_Slice_slice·COSE_Format_cose_signature_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature
    =
        either__Pulse_Lib_Slice_slice·COSE_Format_cose_signature_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature::Inr
        { v: i3 };
    let
    w22:
    (either__Pulse_Lib_Slice_slice·uint8_t_··,
    either__Pulse_Lib_Slice_slice·COSE_Format_cose_signature_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature)
    =
        (w12,w21);
    let
    res1:
    ((empty_or_serialized_map, header_map),
    (either__Pulse_Lib_Slice_slice·uint8_t_··,
    either__Pulse_Lib_Slice_slice·COSE_Format_cose_signature_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature))
    =
        (w11,w22);
    cose_sign_right(res1)
}

/**
Serializer for cose_sign
*/
pub fn
serialize_cose_sign(c: cose_sign, out: &mut [u8]) ->
    usize
{
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let
    _letpattern:
    ((empty_or_serialized_map, header_map),
    (either__Pulse_Lib_Slice_slice·uint8_t_··,
    either__Pulse_Lib_Slice_slice·COSE_Format_cose_signature_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature))
    =
        cose_sign_left(c);
    let res: bool =
        {
            let c1: (empty_or_serialized_map, header_map) = _letpattern.0;
            let
            c2:
            (either__Pulse_Lib_Slice_slice·uint8_t_··,
            either__Pulse_Lib_Slice_slice·COSE_Format_cose_signature_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature)
            =
                _letpattern.1;
            let res1: bool =
                {
                    let c11: empty_or_serialized_map = c1.0;
                    let c21: header_map = c1.1;
                    let count: u64 = (&pcount)[0usize];
                    let res1: bool =
                        if count < 18446744073709551615u64
                        {
                            let size: usize = (&psize)[0usize];
                            let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                            let _out0: &[u8] = _letpattern1.0;
                            let out1: &mut [u8] = _letpattern1.1;
                            let size1: usize = serialize_empty_or_serialized_map(c11, out1);
                            if size1 == 0usize
                            { false }
                            else
                            {
                                (&mut pcount)[0usize] = count.wrapping_add(1u64);
                                (&mut psize)[0usize] = size.wrapping_add(size1);
                                true
                            }
                        }
                        else
                        { false };
                    if res1
                    {
                        let count1: u64 = (&pcount)[0usize];
                        if count1 < 18446744073709551615u64
                        {
                            let size: usize = (&psize)[0usize];
                            let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                            let _out0: &[u8] = _letpattern1.0;
                            let out1: &mut [u8] = _letpattern1.1;
                            let size1: usize = serialize_header_map(c21, out1);
                            if size1 == 0usize
                            { false }
                            else
                            {
                                (&mut pcount)[0usize] = count1.wrapping_add(1u64);
                                (&mut psize)[0usize] = size.wrapping_add(size1);
                                true
                            }
                        }
                        else
                        { false }
                    }
                    else
                    { false }
                };
            if res1
            {
                let c11: either__Pulse_Lib_Slice_slice·uint8_t_·· = c2.0;
                let
                c21:
                either__Pulse_Lib_Slice_slice·COSE_Format_cose_signature_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature
                =
                    c2.1;
                let count: u64 = (&pcount)[0usize];
                let res11: bool =
                    if count < 18446744073709551615u64
                    {
                        let size: usize = (&psize)[0usize];
                        let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                        let _out0: &[u8] = _letpattern1.0;
                        let out1: &mut [u8] = _letpattern1.1;
                        let size1: usize =
                            match c11
                            {
                                either__Pulse_Lib_Slice_slice·uint8_t_··::Inl { v: c12 } =>
                                  serialize_bstr(c12, out1),
                                either__Pulse_Lib_Slice_slice·uint8_t_··::Inr =>
                                  serialize_nil(out1),
                                _ => panic!("Incomplete pattern matching")
                            };
                        if size1 == 0usize
                        { false }
                        else
                        {
                            (&mut pcount)[0usize] = count.wrapping_add(1u64);
                            (&mut psize)[0usize] = size.wrapping_add(size1);
                            true
                        }
                    }
                    else
                    { false };
                if res11
                {
                    let count1: u64 = (&pcount)[0usize];
                    if count1 < 18446744073709551615u64
                    {
                        let size: usize = (&psize)[0usize];
                        let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                        let _out0: &[u8] = _letpattern1.0;
                        let out1: &mut [u8] = _letpattern1.1;
                        let mut pcount1: [u64; 1] = [0u64; 1usize];
                        let mut psize1: [usize; 1] = [0usize; 1usize];
                        let res: bool =
                            match c21
                            {
                                either__Pulse_Lib_Slice_slice·COSE_Format_cose_signature_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature::Inl
                                { v: c12 }
                                =>
                                  if c12.len() == 0usize
                                  { false }
                                  else
                                  {
                                      let mut pres: [bool; 1] = [true; 1usize];
                                      let mut pi: [usize; 1] = [0usize; 1usize];
                                      let slen: usize = c12.len();
                                      let res: bool = (&pres)[0usize];
                                      let i: usize = (&pi)[0usize];
                                      let mut cond: bool = res && i < slen;
                                      while
                                      cond
                                      {
                                          let i0: usize = (&pi)[0usize];
                                          let x: cose_signature = c12[i0];
                                          let res0: bool =
                                              aux_env41_serialize_1(
                                                  x,
                                                  out1,
                                                  &mut pcount1,
                                                  &mut psize1
                                              );
                                          if res0
                                          {
                                              let i·: usize = i0.wrapping_add(1usize);
                                              (&mut pi)[0usize] = i·
                                          }
                                          else
                                          { (&mut pres)[0usize] = false };
                                          let res2: bool = (&pres)[0usize];
                                          let i1: usize = (&pi)[0usize];
                                          cond = res2 && i1 < slen
                                      };
                                      (&pres)[0usize]
                                  },
                                either__Pulse_Lib_Slice_slice·COSE_Format_cose_signature_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature::Inr
                                { v: c22 }
                                =>
                                  {
                                      let em: bool =
                                          crate::cbordetver::cbor_det_array_iterator_is_empty(
                                              c22.cddl_array_iterator_contents
                                          );
                                      if em
                                      { false }
                                      else
                                      {
                                          let
                                          mut
                                          pc:
                                          [array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature;
                                          1]
                                          =
                                              [c22; 1usize];
                                          let mut pres: [bool; 1] = [true; 1usize];
                                          let
                                          c3:
                                          array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature
                                          =
                                              (&pc)[0usize];
                                          let em1: bool =
                                              crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                  c3.cddl_array_iterator_contents
                                              );
                                          let res: bool = (&pres)[0usize];
                                          let mut cond: bool = res && ! em1;
                                          while
                                          cond
                                          {
                                              let
                                              i:
                                              array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature
                                              =
                                                  (&pc)[0usize];
                                              let len0: u64 =
                                                  crate::cbordetver::cbor_det_array_iterator_length(
                                                      i.cddl_array_iterator_contents
                                                  );
                                              let
                                              mut
                                              pj:
                                              [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw;
                                              1]
                                              =
                                                  [i.cddl_array_iterator_contents; 1usize];
                                              let discarded: bool =
                                                  (i.cddl_array_iterator_impl_validate)(&mut pj);
                                              crate::lowstar::ignore::ignore::<bool>(discarded);
                                              let
                                              ji:
                                              crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                              =
                                                  (&pj)[0usize];
                                              let len1: u64 =
                                                  crate::cbordetver::cbor_det_array_iterator_length(
                                                      ji
                                                  );
                                              let
                                              j:
                                              array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature
                                              =
                                                  array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature
                                                  {
                                                      cddl_array_iterator_contents: ji,
                                                      cddl_array_iterator_impl_validate:
                                                      i.cddl_array_iterator_impl_validate,
                                                      cddl_array_iterator_impl_parse:
                                                      i.cddl_array_iterator_impl_parse
                                                  };
                                              (&mut pc)[0usize] = j;
                                              let
                                              tri:
                                              crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                              =
                                                  crate::cbordetver::cbor_det_array_iterator_truncate(
                                                      i.cddl_array_iterator_contents,
                                                      len0.wrapping_sub(len1)
                                                  );
                                              let x: cose_signature =
                                                  (i.cddl_array_iterator_impl_parse)(tri);
                                              let res0: bool =
                                                  aux_env41_serialize_1(
                                                      x,
                                                      out1,
                                                      &mut pcount1,
                                                      &mut psize1
                                                  );
                                              if ! res0 { (&mut pres)[0usize] = false };
                                              let
                                              c30:
                                              array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature
                                              =
                                                  (&pc)[0usize];
                                              let em10: bool =
                                                  crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                      c30.cddl_array_iterator_contents
                                                  );
                                              let res2: bool = (&pres)[0usize];
                                              cond = res2 && ! em10
                                          };
                                          let ret: bool = (&pres)[0usize];
                                          if ret { ret } else { ret }
                                      }
                                  },
                                _ => panic!("Incomplete pattern matching")
                            };
                        let size1: usize =
                            if res
                            {
                                let size1: usize = (&psize1)[0usize];
                                let count2: u64 = (&pcount1)[0usize];
                                crate::cbordetver::cbor_det_serialize_array(count2, out1, size1)
                            }
                            else
                            { 0usize };
                        if size1 == 0usize
                        { false }
                        else
                        {
                            (&mut pcount)[0usize] = count1.wrapping_add(1u64);
                            (&mut psize)[0usize] = size.wrapping_add(size1);
                            true
                        }
                    }
                    else
                    { false }
                }
                else
                { false }
            }
            else
            { false }
        };
    if res
    {
        let size: usize = (&psize)[0usize];
        let count: u64 = (&pcount)[0usize];
        crate::cbordetver::cbor_det_serialize_array(count, out, size)
    }
    else
    { 0usize }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_cose_sign···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (cose_sign <'a>, &'a [u8]) }
}

pub fn validate_and_parse_cose_sign <'a>(s: &'a [u8]) ->
    option__·COSE_Format_cose_sign···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·COSE_Format_cose_sign···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_cose_sign(rl);
              if test
              {
                  let x: cose_sign = parse_cose_sign(rl);
                  option__·COSE_Format_cose_sign···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_cose_sign···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn is_empty_iterate_array_aux_env41_type_1(
    i:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature
) ->
    bool
{ crate::cbordetver::cbor_det_array_iterator_is_empty(i.cddl_array_iterator_contents) }

pub fn next_iterate_array_aux_env41_type_1 <'a>(
    pi:
    &'a mut
    [array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature
    <'a>]
) ->
    cose_signature
    <'a>
{
    let
    i:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature
    =
        pi[0usize];
    let len0: u64 =
        crate::cbordetver::cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
    let mut pj: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [i.cddl_array_iterator_contents; 1usize];
    let discarded: bool = (i.cddl_array_iterator_impl_validate)(&mut pj);
    crate::lowstar::ignore::ignore::<bool>(discarded);
    let ji: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pj)[0usize];
    let len1: u64 = crate::cbordetver::cbor_det_array_iterator_length(ji);
    let
    j:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature
    =
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_cose_signature
        {
            cddl_array_iterator_contents: ji,
            cddl_array_iterator_impl_validate: i.cddl_array_iterator_impl_validate,
            cddl_array_iterator_impl_parse: i.cddl_array_iterator_impl_parse
        };
    pi[0usize] = j;
    let tri: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(
            i.cddl_array_iterator_contents,
            len0.wrapping_sub(len1)
        );
    (i.cddl_array_iterator_impl_parse)(tri)
}

pub fn validate_cose_sign_tagged(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let k: u8 = crate::cbordetver::cbor_det_major_type(c);
    if k == crate::cbordetveraux::cbor_major_type_tagged
    {
        let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let tag·: u64 =
            match v
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 98u64 == tag·
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let c·: crate::cbordetveraux::cbor_raw =
                match v1
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            validate_cose_sign(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub type cose_sign_tagged_ugly <'a> = cose_sign <'a>;

pub type cose_sign_tagged <'a> = cose_sign <'a>;

pub fn cose_sign_tagged_right <'a>(x1: cose_sign <'a>) -> cose_sign <'a> { x1 }

pub fn cose_sign_tagged_left <'a>(x4: cose_sign <'a>) -> cose_sign <'a> { x4 }

/**
Parser for cose_sign_tagged
*/
pub fn
parse_cose_sign_tagged
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    cose_sign
    <'a>
{
    let v: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let cpl: crate::cbordetveraux::cbor_raw =
        match v
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    parse_cose_sign(cpl)
}

/**
Serializer for cose_sign_tagged
*/
pub fn
serialize_cose_sign_tagged(c: cose_sign, out: &mut [u8]) ->
    usize
{
    let c·: (u64, cose_sign) = (98u64,c);
    let ctag: u64 = c·.0;
    let cpayload: cose_sign = c·.1;
    let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
    if tsz == 0usize
    { 0usize }
    else
    {
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
        let _tmp: &[u8] = _letpattern.0;
        let out2: &mut [u8] = _letpattern.1;
        let psz: usize = serialize_cose_sign(cpayload, out2);
        if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
    }
}

pub fn validate_and_parse_cose_sign_tagged <'a>(s: &'a [u8]) ->
    option__·COSE_Format_cose_sign···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·COSE_Format_cose_sign···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let rl: crate::cbordetveraux::cbor_raw = rlrem.0;
              let rem: &[u8] = rlrem.1;
              let test: bool = validate_cose_sign_tagged(rl);
              if test
              {
                  let x: cose_sign = parse_cose_sign_tagged(rl);
                  option__·COSE_Format_cose_sign···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_cose_sign···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}
