#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub fn validate_bool(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    let test: bool = mt == crate::cbordetveraux::cbor_major_type_simple_value;
    let test0: bool =
        if test
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern: crate::cbordetver::cbor_det_view = v1;
            let v10: u8 =
                match _letpattern
                {
                    crate::cbordetver::cbor_det_view::SimpleValue { _0: res } => res,
                    _ => panic!("Incomplete pattern matching")
                };
            v10 == crate::cbordetveraux::cddl_simple_value_false
        }
        else
        { false };
    if test0
    { true }
    else
    {
        let mt0: u8 = crate::cbordetver::cbor_det_major_type(c);
        let test1: bool = mt0 == crate::cbordetveraux::cbor_major_type_simple_value;
        if test1
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern: crate::cbordetver::cbor_det_view = v1;
            let v10: u8 =
                match _letpattern
                {
                    crate::cbordetver::cbor_det_view::SimpleValue { _0: res } => res,
                    _ => panic!("Incomplete pattern matching")
                };
            v10 == crate::cbordetveraux::cddl_simple_value_true
        }
        else
        { false }
    }
}

pub type evercddl_bool_pretty = bool;

pub fn uu___is_Mkevercddl_bool_pretty0(projectee: bool) -> bool
{
    crate::lowstar::ignore::ignore::<bool>(projectee);
    true
}

fn evercddl_bool_pretty_right(x1: bool) -> bool { x1 }

fn evercddl_bool_pretty_left(x3: bool) -> bool { x3 }

/**
Parser for evercddl_bool
*/
pub fn
parse_bool(c: crate::cbordetveraux::cbor_raw) ->
    bool
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let w: u8 =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::SimpleValue { _0: res } => res,
            _ => panic!("Incomplete pattern matching")
        };
    let res: bool = w == crate::cbordetveraux::simple_value_true;
    let res1: bool = res;
    let res2: bool = evercddl_bool_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_bool
*/
pub fn
serialize_bool(c: bool, out: &mut [u8]) ->
    usize
{
    let c·: bool = evercddl_bool_pretty_left(c);
    let c·1: bool = c·;
    if c·1
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
pub enum option__·COSE_Format_evercddl_bool_pretty···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (bool, &'a [u8]) }
}

pub fn validate_and_parse_bool <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_bool_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_bool_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_bool(rl);
              if test
              {
                  let x: bool = parse_bool(rl);
                  option__·COSE_Format_evercddl_bool_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_bool_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_everparsenomatch(c: crate::cbordetveraux::cbor_raw) -> bool
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    false
}

#[derive(PartialEq, Clone, Copy)]
pub enum evercddl_everparsenomatch_pretty
{ Mkevercddl_everparsenomatch_pretty0 }

pub fn uu___is_Mkevercddl_everparsenomatch_pretty0(projectee: evercddl_everparsenomatch_pretty) ->
    bool
{
    crate::lowstar::ignore::ignore::<evercddl_everparsenomatch_pretty>(projectee);
    true
}

fn evercddl_everparsenomatch_pretty_right() -> evercddl_everparsenomatch_pretty
{ evercddl_everparsenomatch_pretty::Mkevercddl_everparsenomatch_pretty0 }

/**
Parser for evercddl_everparsenomatch
*/
pub fn
parse_everparsenomatch(c: crate::cbordetveraux::cbor_raw) ->
    evercddl_everparsenomatch_pretty
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    let res2: evercddl_everparsenomatch_pretty = evercddl_everparsenomatch_pretty_right();
    res2
}

/**
Serializer for evercddl_everparsenomatch
*/
pub fn
serialize_everparsenomatch(c: evercddl_everparsenomatch_pretty, out: &[u8]) ->
    usize
{
    crate::lowstar::ignore::ignore::<evercddl_everparsenomatch_pretty>(c);
    crate::lowstar::ignore::ignore::<&[u8]>(out);
    0usize
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_everparsenomatch_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_everparsenomatch_pretty, &'a [u8]) }
}

pub fn validate_and_parse_everparsenomatch <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_everparsenomatch_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_everparsenomatch_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_everparsenomatch(rl);
              if test
              {
                  let x: evercddl_everparsenomatch_pretty = parse_everparsenomatch(rl);
                  option__·COSE_Format_evercddl_everparsenomatch_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_everparsenomatch_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_uint(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    mt == crate::cbordetveraux::cbor_major_type_uint64
}

pub type evercddl_uint_pretty = u64;

pub fn uu___is_Mkevercddl_uint_pretty0(projectee: u64) -> bool
{
    crate::lowstar::ignore::ignore::<u64>(projectee);
    true
}

fn evercddl_uint_pretty_right(x1: u64) -> u64 { x1 }

fn evercddl_uint_pretty_left(x3: u64) -> u64 { x3 }

/**
Parser for evercddl_uint
*/
pub fn
parse_uint(c: crate::cbordetveraux::cbor_raw) ->
    u64
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let res: u64 =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
            _ => panic!("Incomplete pattern matching")
        };
    let res0: u64 = res;
    let res1: u64 = res0;
    let res2: u64 = evercddl_uint_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_uint
*/
pub fn
serialize_uint(c: u64, out: &mut [u8]) ->
    usize
{
    let c·: u64 = evercddl_uint_pretty_left(c);
    let mty: crate::cbordetver::cbor_det_int_kind = crate::cbordetver::cbor_det_int_kind::UInt64;
    let x: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty, c·);
    let ser: crate::cbordetver::option__size_t = crate::cbordetver::cbor_det_serialize(x, out);
    match ser
    {
        crate::cbordetver::option__size_t::None => 0usize,
        crate::cbordetver::option__size_t::Some { v: sz } => sz,
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_uint_pretty···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (u64, &'a [u8]) }
}

pub fn validate_and_parse_uint <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_uint_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_uint_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_uint(rl);
              if test
              {
                  let x: u64 = parse_uint(rl);
                  option__·COSE_Format_evercddl_uint_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_uint_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_nint(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    mt == crate::cbordetveraux::cbor_major_type_neg_int64
}

pub type evercddl_nint_pretty = u64;

pub fn uu___is_Mkevercddl_nint_pretty0(projectee: u64) -> bool
{
    crate::lowstar::ignore::ignore::<u64>(projectee);
    true
}

fn evercddl_nint_pretty_right(x1: u64) -> u64 { x1 }

fn evercddl_nint_pretty_left(x3: u64) -> u64 { x3 }

/**
Parser for evercddl_nint
*/
pub fn
parse_nint(c: crate::cbordetveraux::cbor_raw) ->
    u64
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let res: u64 =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
            _ => panic!("Incomplete pattern matching")
        };
    let res0: u64 = res;
    let res1: u64 = res0;
    let res2: u64 = evercddl_nint_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_nint
*/
pub fn
serialize_nint(c: u64, out: &mut [u8]) ->
    usize
{
    let c·: u64 = evercddl_nint_pretty_left(c);
    let mty: crate::cbordetver::cbor_det_int_kind =
        if
        crate::cbordetveraux::cbor_major_type_neg_int64
        ==
        crate::cbordetveraux::cbor_major_type_uint64
        { crate::cbordetver::cbor_det_int_kind::UInt64 }
        else
        { crate::cbordetver::cbor_det_int_kind::NegInt64 };
    let x: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty, c·);
    let ser: crate::cbordetver::option__size_t = crate::cbordetver::cbor_det_serialize(x, out);
    match ser
    {
        crate::cbordetver::option__size_t::None => 0usize,
        crate::cbordetver::option__size_t::Some { v: sz } => sz,
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_nint_pretty···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (u64, &'a [u8]) }
}

pub fn validate_and_parse_nint <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_nint_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_nint_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_nint(rl);
              if test
              {
                  let x: u64 = parse_nint(rl);
                  option__·COSE_Format_evercddl_nint_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_nint_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_int(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let test: bool = validate_uint(c);
    if test { true } else { validate_nint(c) }
}

#[derive(PartialEq, Clone, Copy)]
pub enum evercddl_int_tags
{
    Inl,
    Inr
}

#[derive(PartialEq, Clone, Copy)]
enum evercddl_int
{
    Inl { v: u64 },
    Inr { v: u64 }
}

#[derive(PartialEq, Clone, Copy)]
enum evercddl_int_pretty_tags
{
    Mkevercddl_int_pretty0,
    Mkevercddl_int_pretty1
}

#[derive(PartialEq, Clone, Copy)]
pub enum evercddl_int_pretty
{
    Mkevercddl_int_pretty0 { _x0: u64 },
    Mkevercddl_int_pretty1 { _x0: u64 }
}

pub fn uu___is_Mkevercddl_int_pretty0(projectee: evercddl_int_pretty) -> bool
{ match projectee { evercddl_int_pretty::Mkevercddl_int_pretty0 { .. } => true, _ => false } }

pub fn uu___is_Mkevercddl_int_pretty1(projectee: evercddl_int_pretty) -> bool
{ match projectee { evercddl_int_pretty::Mkevercddl_int_pretty1 { .. } => true, _ => false } }

fn evercddl_int_pretty_right(x2: evercddl_int) -> evercddl_int_pretty
{
    match x2
    {
        evercddl_int::Inl { v: x3 } => evercddl_int_pretty::Mkevercddl_int_pretty0 { _x0: x3 },
        evercddl_int::Inr { v: x4 } => evercddl_int_pretty::Mkevercddl_int_pretty1 { _x0: x4 },
        _ => panic!("Incomplete pattern matching")
    }
}

fn evercddl_int_pretty_left(x7: evercddl_int_pretty) -> evercddl_int
{
    match x7
    {
        evercddl_int_pretty::Mkevercddl_int_pretty0 { _x0: x10 } => evercddl_int::Inl { v: x10 },
        evercddl_int_pretty::Mkevercddl_int_pretty1 { _x0: x12 } => evercddl_int::Inr { v: x12 },
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Parser for evercddl_int
*/
pub fn
parse_int(c: crate::cbordetveraux::cbor_raw) ->
    evercddl_int_pretty
{
    let test: bool = validate_uint(c);
    let res1: evercddl_int =
        if test
        {
            let res: u64 = parse_uint(c);
            evercddl_int::Inl { v: res }
        }
        else
        {
            let res: u64 = parse_nint(c);
            evercddl_int::Inr { v: res }
        };
    let res2: evercddl_int_pretty = evercddl_int_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_int
*/
pub fn
serialize_int(c: evercddl_int_pretty, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_int = evercddl_int_pretty_left(c);
    match c·
    {
        evercddl_int::Inl { v: c1 } =>
          {
              let res: usize = serialize_uint(c1, out);
              res
          },
        evercddl_int::Inr { v: c2 } =>
          {
              let res: usize = serialize_nint(c2, out);
              res
          },
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_int_pretty···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_int_pretty, &'a [u8]) }
}

pub fn validate_and_parse_int <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_int_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_int_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_int(rl);
              if test
              {
                  let x: evercddl_int_pretty = parse_int(rl);
                  option__·COSE_Format_evercddl_int_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_int_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_bstr(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    mt == crate::cbordetveraux::cbor_major_type_byte_string
}

pub type evercddl_bstr <'a> = &'a [u8];

pub type evercddl_bstr_pretty <'a> = evercddl_bstr <'a>;

pub fn uu___is_Mkevercddl_bstr_pretty0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_bstr_pretty_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_bstr_pretty_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

/**
Parser for evercddl_bstr
*/
pub fn
parse_bstr
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let s: &[u8] =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let res1: &[u8] = s;
    let res2: &[u8] = evercddl_bstr_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_bstr
*/
pub fn
serialize_bstr(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_bstr_pretty_left(c);
    let len: usize = c·.len();
    if len <= 18446744073709551615u64 as usize
    {
        let mty: crate::cbordetver::cbor_det_string_kind =
            crate::cbordetver::cbor_det_string_kind::ByteString;
        let res: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
            crate::cbordetver::cbor_det_mk_string(mty, c·);
        let _letpattern: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = res;
        let x: crate::cbordetveraux::cbor_raw =
            match _letpattern
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

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_bstr_pretty···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_bstr <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_bstr_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_bstr_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_bstr(rl);
              if test
              {
                  let x: &[u8] = parse_bstr(rl);
                  option__·COSE_Format_evercddl_bstr_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_bstr_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
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
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let tag·: u64 =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 24u64 == tag·
        {
            let v10: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern0: crate::cbordetver::cbor_det_view = v10;
            let c·: crate::cbordetveraux::cbor_raw =
                match _letpattern0
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let res: bool = validate_bstr(c·);
            res
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_encodedcbor_pretty <'a> = evercddl_bstr_pretty <'a>;

pub fn uu___is_Mkevercddl_encodedcbor_pretty0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_encodedcbor_pretty_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_encodedcbor_pretty_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

/**
Parser for evercddl_encodedcbor
*/
pub fn
parse_encodedcbor
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let cpl: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let res: &[u8] = parse_bstr(cpl);
    let res1: &[u8] = res;
    let res2: &[u8] = evercddl_encodedcbor_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_encodedcbor
*/
pub fn
serialize_encodedcbor(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_encodedcbor_pretty_left(c);
    let c·1: (u64, &[u8]) = (24u64,c·);
    let _letpattern: (u64, &[u8]) = c·1;
    let res: usize =
        {
            let ctag: u64 = _letpattern.0;
            let cpayload: &[u8] = _letpattern.1;
            let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
            if tsz == 0usize
            { 0usize }
            else
            {
                let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
                let out2: &mut [u8] = _letpattern1.1;
                let psz: usize = serialize_bstr(cpayload, out2);
                if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
            }
        };
    let res0: usize = res;
    res0
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_encodedcbor_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_encodedcbor <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_encodedcbor_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_encodedcbor_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_encodedcbor(rl);
              if test
              {
                  let x: &[u8] = parse_encodedcbor(rl);
                  option__·COSE_Format_evercddl_encodedcbor_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_encodedcbor_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_bytes(c: crate::cbordetveraux::cbor_raw) -> bool { validate_bstr(c) }

pub type evercddl_bytes_pretty <'a> = evercddl_bstr_pretty <'a>;

pub fn uu___is_Mkevercddl_bytes_pretty0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_bytes_pretty_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_bytes_pretty_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

/**
Parser for evercddl_bytes
*/
pub fn
parse_bytes
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let res1: &[u8] = parse_bstr(c);
    let res2: &[u8] = evercddl_bytes_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_bytes
*/
pub fn
serialize_bytes(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_bytes_pretty_left(c);
    let res: usize = serialize_bstr(c·, out);
    res
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_bytes_pretty···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_bytes <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_bytes_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_bytes_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_bytes(rl);
              if test
              {
                  let x: &[u8] = parse_bytes(rl);
                  option__·COSE_Format_evercddl_bytes_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_bytes_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_tstr(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    mt == crate::cbordetveraux::cbor_major_type_text_string
}

pub type evercddl_tstr_pretty <'a> = evercddl_bstr <'a>;

pub fn uu___is_Mkevercddl_tstr_pretty0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_tstr_pretty_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_tstr_pretty_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

/**
Parser for evercddl_tstr
*/
pub fn
parse_tstr
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let s: &[u8] =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let res1: &[u8] = s;
    let res2: &[u8] = evercddl_tstr_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_tstr
*/
pub fn
serialize_tstr(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_tstr_pretty_left(c);
    let len: usize = c·.len();
    if len <= 18446744073709551615u64 as usize
    {
        let correct: bool = crate::cbordetver::cbor_impl_utf8_correct(c·);
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
                crate::cbordetver::cbor_det_mk_string(mty, c·);
            let _letpattern: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = res;
            let x: crate::cbordetveraux::cbor_raw =
                match _letpattern
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

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_tstr_pretty···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_tstr <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_tstr_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_tstr_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_tstr(rl);
              if test
              {
                  let x: &[u8] = parse_tstr(rl);
                  option__·COSE_Format_evercddl_tstr_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_tstr_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_label(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let test: bool = validate_int(c);
    if test { true } else { validate_tstr(c) }
}

#[derive(PartialEq, Clone, Copy)]
pub enum evercddl_label <'a>
{
    Inl { v: evercddl_int_pretty },
    Inr { v: &'a [u8] }
}

#[derive(PartialEq, Clone, Copy)]
enum evercddl_label_pretty_tags
{
    Mkevercddl_label_pretty0,
    Mkevercddl_label_pretty1
}

#[derive(PartialEq, Clone, Copy)]
pub enum evercddl_label_pretty <'a>
{
    Mkevercddl_label_pretty0 { _x0: evercddl_int_pretty },
    Mkevercddl_label_pretty1 { _x0: &'a [u8] }
}

pub fn uu___is_Mkevercddl_label_pretty0(projectee: evercddl_label_pretty) -> bool
{
    match projectee { evercddl_label_pretty::Mkevercddl_label_pretty0 { .. } => true, _ => false }
}

pub fn uu___is_Mkevercddl_label_pretty1(projectee: evercddl_label_pretty) -> bool
{
    match projectee { evercddl_label_pretty::Mkevercddl_label_pretty1 { .. } => true, _ => false }
}

fn evercddl_label_pretty_right <'a>(x2: evercddl_label <'a>) -> evercddl_label_pretty <'a>
{
    match x2
    {
        evercddl_label::Inl { v: x3 } => evercddl_label_pretty::Mkevercddl_label_pretty0 { _x0: x3 },
        evercddl_label::Inr { v: x4 } => evercddl_label_pretty::Mkevercddl_label_pretty1 { _x0: x4 },
        _ => panic!("Incomplete pattern matching")
    }
}

fn evercddl_label_pretty_left <'a>(x7: evercddl_label_pretty <'a>) -> evercddl_label <'a>
{
    match x7
    {
        evercddl_label_pretty::Mkevercddl_label_pretty0 { _x0: x10 } =>
          evercddl_label::Inl { v: x10 },
        evercddl_label_pretty::Mkevercddl_label_pretty1 { _x0: x12 } =>
          evercddl_label::Inr { v: x12 },
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Parser for evercddl_label
*/
pub fn
parse_label
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_label_pretty
    <'a>
{
    let test: bool = validate_int(c);
    let res1: evercddl_label =
        if test
        {
            let res: evercddl_int_pretty = parse_int(c);
            evercddl_label::Inl { v: res }
        }
        else
        {
            let res: &[u8] = parse_tstr(c);
            evercddl_label::Inr { v: res }
        };
    let res2: evercddl_label_pretty = evercddl_label_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_label
*/
pub fn
serialize_label(c: evercddl_label_pretty, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_label = evercddl_label_pretty_left(c);
    match c·
    {
        evercddl_label::Inl { v: c1 } =>
          {
              let res: usize = serialize_int(c1, out);
              res
          },
        evercddl_label::Inr { v: c2 } =>
          {
              let res: usize = serialize_tstr(c2, out);
              res
          },
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_label_pretty···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_label_pretty <'a>, &'a [u8]) }
}

pub fn validate_and_parse_label <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_label_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_label_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_label(rl);
              if test
              {
                  let x: evercddl_label_pretty = parse_label(rl);
                  option__·COSE_Format_evercddl_label_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_label_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_tdate(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let k: u8 = crate::cbordetver::cbor_det_major_type(c);
    if k == crate::cbordetveraux::cbor_major_type_tagged
    {
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let tag·: u64 =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 0u64 == tag·
        {
            let v10: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern0: crate::cbordetver::cbor_det_view = v10;
            let c·: crate::cbordetveraux::cbor_raw =
                match _letpattern0
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let res: bool = validate_tstr(c·);
            res
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_tdate_pretty <'a> = evercddl_tstr_pretty <'a>;

pub fn uu___is_Mkevercddl_tdate_pretty0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_tdate_pretty_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_tdate_pretty_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

/**
Parser for evercddl_tdate
*/
pub fn
parse_tdate
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let cpl: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let res: &[u8] = parse_tstr(cpl);
    let res1: &[u8] = res;
    let res2: &[u8] = evercddl_tdate_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_tdate
*/
pub fn
serialize_tdate(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_tdate_pretty_left(c);
    let c·1: (u64, &[u8]) = (0u64,c·);
    let _letpattern: (u64, &[u8]) = c·1;
    let res: usize =
        {
            let ctag: u64 = _letpattern.0;
            let cpayload: &[u8] = _letpattern.1;
            let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
            if tsz == 0usize
            { 0usize }
            else
            {
                let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
                let out2: &mut [u8] = _letpattern1.1;
                let psz: usize = serialize_tstr(cpayload, out2);
                if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
            }
        };
    let res0: usize = res;
    res0
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_tdate_pretty···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_tdate <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_tdate_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_tdate_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_tdate(rl);
              if test
              {
                  let x: &[u8] = parse_tdate(rl);
                  option__·COSE_Format_evercddl_tdate_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_tdate_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
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
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let tag·: u64 =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 32u64 == tag·
        {
            let v10: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern0: crate::cbordetver::cbor_det_view = v10;
            let c·: crate::cbordetveraux::cbor_raw =
                match _letpattern0
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let res: bool = validate_tstr(c·);
            res
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_uri_pretty <'a> = evercddl_tstr_pretty <'a>;

pub fn uu___is_Mkevercddl_uri_pretty0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_uri_pretty_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_uri_pretty_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

/**
Parser for evercddl_uri
*/
pub fn
parse_uri
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let cpl: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let res: &[u8] = parse_tstr(cpl);
    let res1: &[u8] = res;
    let res2: &[u8] = evercddl_uri_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_uri
*/
pub fn
serialize_uri(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_uri_pretty_left(c);
    let c·1: (u64, &[u8]) = (32u64,c·);
    let _letpattern: (u64, &[u8]) = c·1;
    let res: usize =
        {
            let ctag: u64 = _letpattern.0;
            let cpayload: &[u8] = _letpattern.1;
            let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
            if tsz == 0usize
            { 0usize }
            else
            {
                let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
                let out2: &mut [u8] = _letpattern1.1;
                let psz: usize = serialize_tstr(cpayload, out2);
                if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
            }
        };
    let res0: usize = res;
    res0
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_uri_pretty···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_uri <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_uri_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_uri_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_uri(rl);
              if test
              {
                  let x: &[u8] = parse_uri(rl);
                  option__·COSE_Format_evercddl_uri_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_uri_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
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
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let tag·: u64 =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 33u64 == tag·
        {
            let v10: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern0: crate::cbordetver::cbor_det_view = v10;
            let c·: crate::cbordetveraux::cbor_raw =
                match _letpattern0
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let res: bool = validate_tstr(c·);
            res
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_b64url_pretty <'a> = evercddl_tstr_pretty <'a>;

pub fn uu___is_Mkevercddl_b64url_pretty0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_b64url_pretty_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_b64url_pretty_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

/**
Parser for evercddl_b64url
*/
pub fn
parse_b64url
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let cpl: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let res: &[u8] = parse_tstr(cpl);
    let res1: &[u8] = res;
    let res2: &[u8] = evercddl_b64url_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_b64url
*/
pub fn
serialize_b64url(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_b64url_pretty_left(c);
    let c·1: (u64, &[u8]) = (33u64,c·);
    let _letpattern: (u64, &[u8]) = c·1;
    let res: usize =
        {
            let ctag: u64 = _letpattern.0;
            let cpayload: &[u8] = _letpattern.1;
            let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
            if tsz == 0usize
            { 0usize }
            else
            {
                let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
                let out2: &mut [u8] = _letpattern1.1;
                let psz: usize = serialize_tstr(cpayload, out2);
                if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
            }
        };
    let res0: usize = res;
    res0
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_b64url_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_b64url <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_b64url_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_b64url_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_b64url(rl);
              if test
              {
                  let x: &[u8] = parse_b64url(rl);
                  option__·COSE_Format_evercddl_b64url_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_b64url_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
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
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let tag·: u64 =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 34u64 == tag·
        {
            let v10: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern0: crate::cbordetver::cbor_det_view = v10;
            let c·: crate::cbordetveraux::cbor_raw =
                match _letpattern0
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let res: bool = validate_tstr(c·);
            res
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_b64legacy_pretty <'a> = evercddl_tstr_pretty <'a>;

pub fn uu___is_Mkevercddl_b64legacy_pretty0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_b64legacy_pretty_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_b64legacy_pretty_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

/**
Parser for evercddl_b64legacy
*/
pub fn
parse_b64legacy
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let cpl: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let res: &[u8] = parse_tstr(cpl);
    let res1: &[u8] = res;
    let res2: &[u8] = evercddl_b64legacy_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_b64legacy
*/
pub fn
serialize_b64legacy(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_b64legacy_pretty_left(c);
    let c·1: (u64, &[u8]) = (34u64,c·);
    let _letpattern: (u64, &[u8]) = c·1;
    let res: usize =
        {
            let ctag: u64 = _letpattern.0;
            let cpayload: &[u8] = _letpattern.1;
            let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
            if tsz == 0usize
            { 0usize }
            else
            {
                let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
                let out2: &mut [u8] = _letpattern1.1;
                let psz: usize = serialize_tstr(cpayload, out2);
                if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
            }
        };
    let res0: usize = res;
    res0
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_b64legacy_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_b64legacy <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_b64legacy_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_b64legacy_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_b64legacy(rl);
              if test
              {
                  let x: &[u8] = parse_b64legacy(rl);
                  option__·COSE_Format_evercddl_b64legacy_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_b64legacy_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
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
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let tag·: u64 =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 35u64 == tag·
        {
            let v10: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern0: crate::cbordetver::cbor_det_view = v10;
            let c·: crate::cbordetveraux::cbor_raw =
                match _letpattern0
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let res: bool = validate_tstr(c·);
            res
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_regexp_pretty <'a> = evercddl_tstr_pretty <'a>;

pub fn uu___is_Mkevercddl_regexp_pretty0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_regexp_pretty_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_regexp_pretty_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

/**
Parser for evercddl_regexp
*/
pub fn
parse_regexp
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let cpl: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let res: &[u8] = parse_tstr(cpl);
    let res1: &[u8] = res;
    let res2: &[u8] = evercddl_regexp_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_regexp
*/
pub fn
serialize_regexp(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_regexp_pretty_left(c);
    let c·1: (u64, &[u8]) = (35u64,c·);
    let _letpattern: (u64, &[u8]) = c·1;
    let res: usize =
        {
            let ctag: u64 = _letpattern.0;
            let cpayload: &[u8] = _letpattern.1;
            let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
            if tsz == 0usize
            { 0usize }
            else
            {
                let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
                let out2: &mut [u8] = _letpattern1.1;
                let psz: usize = serialize_tstr(cpayload, out2);
                if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
            }
        };
    let res0: usize = res;
    res0
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_regexp_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_regexp <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_regexp_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_regexp_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_regexp(rl);
              if test
              {
                  let x: &[u8] = parse_regexp(rl);
                  option__·COSE_Format_evercddl_regexp_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_regexp_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
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
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let tag·: u64 =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 36u64 == tag·
        {
            let v10: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern0: crate::cbordetver::cbor_det_view = v10;
            let c·: crate::cbordetveraux::cbor_raw =
                match _letpattern0
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let res: bool = validate_tstr(c·);
            res
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_mimemessage_pretty <'a> = evercddl_tstr_pretty <'a>;

pub fn uu___is_Mkevercddl_mimemessage_pretty0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_mimemessage_pretty_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_mimemessage_pretty_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

/**
Parser for evercddl_mimemessage
*/
pub fn
parse_mimemessage
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let cpl: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let res: &[u8] = parse_tstr(cpl);
    let res1: &[u8] = res;
    let res2: &[u8] = evercddl_mimemessage_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_mimemessage
*/
pub fn
serialize_mimemessage(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_mimemessage_pretty_left(c);
    let c·1: (u64, &[u8]) = (36u64,c·);
    let _letpattern: (u64, &[u8]) = c·1;
    let res: usize =
        {
            let ctag: u64 = _letpattern.0;
            let cpayload: &[u8] = _letpattern.1;
            let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
            if tsz == 0usize
            { 0usize }
            else
            {
                let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
                let out2: &mut [u8] = _letpattern1.1;
                let psz: usize = serialize_tstr(cpayload, out2);
                if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
            }
        };
    let res0: usize = res;
    res0
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_mimemessage_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_mimemessage <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_mimemessage_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_mimemessage_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_mimemessage(rl);
              if test
              {
                  let x: &[u8] = parse_mimemessage(rl);
                  option__·COSE_Format_evercddl_mimemessage_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_mimemessage_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_text(c: crate::cbordetveraux::cbor_raw) -> bool { validate_tstr(c) }

pub type evercddl_text_pretty <'a> = evercddl_tstr_pretty <'a>;

pub fn uu___is_Mkevercddl_text_pretty0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_text_pretty_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_text_pretty_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

/**
Parser for evercddl_text
*/
pub fn
parse_text
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let res1: &[u8] = parse_tstr(c);
    let res2: &[u8] = evercddl_text_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_text
*/
pub fn
serialize_text(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_text_pretty_left(c);
    let res: usize = serialize_tstr(c·, out);
    res
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_text_pretty···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_text <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_text_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_text_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_text(rl);
              if test
              {
                  let x: &[u8] = parse_text(rl);
                  option__·COSE_Format_evercddl_text_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_text_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
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
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let v10: u8 =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::SimpleValue { _0: res } => res,
                _ => panic!("Incomplete pattern matching")
            };
        v10 == 20u8
    }
    else
    { false }
}

#[derive(PartialEq, Clone, Copy)] pub enum evercddl_false_pretty { Mkevercddl_false_pretty0 }

pub fn uu___is_Mkevercddl_false_pretty0(projectee: evercddl_false_pretty) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_false_pretty>(projectee);
    true
}

fn evercddl_false_pretty_right() -> evercddl_false_pretty
{ evercddl_false_pretty::Mkevercddl_false_pretty0 }

/**
Parser for evercddl_false
*/
pub fn
parse_false(c: crate::cbordetveraux::cbor_raw) ->
    evercddl_false_pretty
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    let res2: evercddl_false_pretty = evercddl_false_pretty_right();
    res2
}

/**
Serializer for evercddl_false
*/
pub fn
serialize_false(c: evercddl_false_pretty, out: &mut [u8]) ->
    usize
{
    crate::lowstar::ignore::ignore::<evercddl_false_pretty>(c);
    let _letpattern: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_mk_simple_value(20u8);
    let c1: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res } => res,
            _ => panic!("Incomplete pattern matching")
        };
    let res: crate::cbordetver::option__size_t = crate::cbordetver::cbor_det_serialize(c1, out);
    let res0: usize =
        match res
        {
            crate::cbordetver::option__size_t::None => 0usize,
            crate::cbordetver::option__size_t::Some { v: r } => r,
            _ => panic!("Incomplete pattern matching")
        };
    let res1: usize = res0;
    res1
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_false_pretty···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_false_pretty, &'a [u8]) }
}

pub fn validate_and_parse_false <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_false_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_false_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_false(rl);
              if test
              {
                  let x: evercddl_false_pretty = parse_false(rl);
                  option__·COSE_Format_evercddl_false_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_false_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
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
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let v10: u8 =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::SimpleValue { _0: res } => res,
                _ => panic!("Incomplete pattern matching")
            };
        v10 == 21u8
    }
    else
    { false }
}

#[derive(PartialEq, Clone, Copy)] pub enum evercddl_true_pretty { Mkevercddl_true_pretty0 }

pub fn uu___is_Mkevercddl_true_pretty0(projectee: evercddl_true_pretty) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_true_pretty>(projectee);
    true
}

fn evercddl_true_pretty_right() -> evercddl_true_pretty
{ evercddl_true_pretty::Mkevercddl_true_pretty0 }

/**
Parser for evercddl_true
*/
pub fn
parse_true(c: crate::cbordetveraux::cbor_raw) ->
    evercddl_true_pretty
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    let res2: evercddl_true_pretty = evercddl_true_pretty_right();
    res2
}

/**
Serializer for evercddl_true
*/
pub fn
serialize_true(c: evercddl_true_pretty, out: &mut [u8]) ->
    usize
{
    crate::lowstar::ignore::ignore::<evercddl_true_pretty>(c);
    let _letpattern: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_mk_simple_value(21u8);
    let c1: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res } => res,
            _ => panic!("Incomplete pattern matching")
        };
    let res: crate::cbordetver::option__size_t = crate::cbordetver::cbor_det_serialize(c1, out);
    let res0: usize =
        match res
        {
            crate::cbordetver::option__size_t::None => 0usize,
            crate::cbordetver::option__size_t::Some { v: r } => r,
            _ => panic!("Incomplete pattern matching")
        };
    let res1: usize = res0;
    res1
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_true_pretty···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_true_pretty, &'a [u8]) }
}

pub fn validate_and_parse_true <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_true_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_true_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_true(rl);
              if test
              {
                  let x: evercddl_true_pretty = parse_true(rl);
                  option__·COSE_Format_evercddl_true_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_true_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_nil(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    let test: bool = mt == crate::cbordetveraux::cbor_major_type_simple_value;
    if test
    {
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let v10: u8 =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::SimpleValue { _0: res } => res,
                _ => panic!("Incomplete pattern matching")
            };
        v10 == 22u8
    }
    else
    { false }
}

#[derive(PartialEq, Clone, Copy)] pub enum evercddl_nil_pretty { Mkevercddl_nil_pretty0 }

pub fn uu___is_Mkevercddl_nil_pretty0(projectee: evercddl_nil_pretty) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_nil_pretty>(projectee);
    true
}

fn evercddl_nil_pretty_right() -> evercddl_nil_pretty
{ evercddl_nil_pretty::Mkevercddl_nil_pretty0 }

/**
Parser for evercddl_nil
*/
pub fn
parse_nil(c: crate::cbordetveraux::cbor_raw) ->
    evercddl_nil_pretty
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    let res2: evercddl_nil_pretty = evercddl_nil_pretty_right();
    res2
}

/**
Serializer for evercddl_nil
*/
pub fn
serialize_nil(c: evercddl_nil_pretty, out: &mut [u8]) ->
    usize
{
    crate::lowstar::ignore::ignore::<evercddl_nil_pretty>(c);
    let _letpattern: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_mk_simple_value(22u8);
    let c1: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res } => res,
            _ => panic!("Incomplete pattern matching")
        };
    let res: crate::cbordetver::option__size_t = crate::cbordetver::cbor_det_serialize(c1, out);
    let res0: usize =
        match res
        {
            crate::cbordetver::option__size_t::None => 0usize,
            crate::cbordetver::option__size_t::Some { v: r } => r,
            _ => panic!("Incomplete pattern matching")
        };
    let res1: usize = res0;
    res1
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_nil_pretty···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_nil_pretty, &'a [u8]) }
}

pub fn validate_and_parse_nil <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_nil_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_nil_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_nil(rl);
              if test
              {
                  let x: evercddl_nil_pretty = parse_nil(rl);
                  option__·COSE_Format_evercddl_nil_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_nil_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_null(c: crate::cbordetveraux::cbor_raw) -> bool { validate_nil(c) }

pub type evercddl_null_pretty = evercddl_nil_pretty;

pub fn uu___is_Mkevercddl_null_pretty0(projectee: evercddl_nil_pretty) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_nil_pretty>(projectee);
    true
}

fn evercddl_null_pretty_right(x1: evercddl_nil_pretty) -> evercddl_nil_pretty { x1 }

fn evercddl_null_pretty_left(x3: evercddl_nil_pretty) -> evercddl_nil_pretty { x3 }

/**
Parser for evercddl_null
*/
pub fn
parse_null(c: crate::cbordetveraux::cbor_raw) ->
    evercddl_nil_pretty
{
    let res1: evercddl_nil_pretty = parse_nil(c);
    let res2: evercddl_nil_pretty = evercddl_null_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_null
*/
pub fn
serialize_null(c: evercddl_nil_pretty, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_nil_pretty = evercddl_null_pretty_left(c);
    let res: usize = serialize_nil(c·, out);
    res
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_null_pretty···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_nil_pretty, &'a [u8]) }
}

pub fn validate_and_parse_null <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_null_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_null_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_null(rl);
              if test
              {
                  let x: evercddl_nil_pretty = parse_null(rl);
                  option__·COSE_Format_evercddl_null_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_null_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
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
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let v10: u8 =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::SimpleValue { _0: res } => res,
                _ => panic!("Incomplete pattern matching")
            };
        v10 == 23u8
    }
    else
    { false }
}

#[derive(PartialEq, Clone, Copy)]
pub enum evercddl_undefined_pretty
{ Mkevercddl_undefined_pretty0 }

pub fn uu___is_Mkevercddl_undefined_pretty0(projectee: evercddl_undefined_pretty) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_undefined_pretty>(projectee);
    true
}

fn evercddl_undefined_pretty_right() -> evercddl_undefined_pretty
{ evercddl_undefined_pretty::Mkevercddl_undefined_pretty0 }

/**
Parser for evercddl_undefined
*/
pub fn
parse_undefined(c: crate::cbordetveraux::cbor_raw) ->
    evercddl_undefined_pretty
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    let res2: evercddl_undefined_pretty = evercddl_undefined_pretty_right();
    res2
}

/**
Serializer for evercddl_undefined
*/
pub fn
serialize_undefined(c: evercddl_undefined_pretty, out: &mut [u8]) ->
    usize
{
    crate::lowstar::ignore::ignore::<evercddl_undefined_pretty>(c);
    let _letpattern: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_mk_simple_value(23u8);
    let c1: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res } => res,
            _ => panic!("Incomplete pattern matching")
        };
    let res: crate::cbordetver::option__size_t = crate::cbordetver::cbor_det_serialize(c1, out);
    let res0: usize =
        match res
        {
            crate::cbordetver::option__size_t::None => 0usize,
            crate::cbordetver::option__size_t::Some { v: r } => r,
            _ => panic!("Incomplete pattern matching")
        };
    let res1: usize = res0;
    res1
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_undefined_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_undefined_pretty, &'a [u8]) }
}

pub fn validate_and_parse_undefined <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_undefined_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_undefined_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_undefined(rl);
              if test
              {
                  let x: evercddl_undefined_pretty = parse_undefined(rl);
                  option__·COSE_Format_evercddl_undefined_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_undefined_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_any(c: crate::cbordetveraux::cbor_raw) -> bool
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    true
}

pub type evercddl_any <'a> = crate::cbordetveraux::cbor_raw <'a>;

pub type evercddl_any_pretty <'a> = evercddl_any <'a>;

pub fn uu___is_Mkevercddl_any_pretty0(projectee: crate::cbordetveraux::cbor_raw) -> bool
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(projectee);
    true
}

fn evercddl_any_pretty_right <'a>(x1: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x1 }

fn evercddl_any_pretty_left <'a>(x3: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x3 }

/**
Parser for evercddl_any
*/
pub fn
parse_any
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{
    let res1: crate::cbordetveraux::cbor_raw = c;
    let res2: crate::cbordetveraux::cbor_raw = evercddl_any_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_any
*/
pub fn
serialize_any(c: crate::cbordetveraux::cbor_raw, out: &mut [u8]) ->
    usize
{
    let c·: crate::cbordetveraux::cbor_raw = evercddl_any_pretty_left(c);
    let ser: crate::cbordetver::option__size_t = crate::cbordetver::cbor_det_serialize(c·, out);
    match ser
    {
        crate::cbordetver::option__size_t::None => 0usize,
        crate::cbordetver::option__size_t::Some { v: sz } => sz,
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_any_pretty···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (crate::cbordetveraux::cbor_raw <'a>, &'a [u8]) }
}

pub fn validate_and_parse_any <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_any_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_any_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_any(rl);
              if test
              {
                  let x: crate::cbordetveraux::cbor_raw = parse_any(rl);
                  option__·COSE_Format_evercddl_any_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_any_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_values(c: crate::cbordetveraux::cbor_raw) -> bool { validate_any(c) }

pub type evercddl_values_pretty <'a> = evercddl_any_pretty <'a>;

pub fn uu___is_Mkevercddl_values_pretty0(projectee: crate::cbordetveraux::cbor_raw) -> bool
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(projectee);
    true
}

fn evercddl_values_pretty_right <'a>(x1: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x1 }

fn evercddl_values_pretty_left <'a>(x3: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x3 }

/**
Parser for evercddl_values
*/
pub fn
parse_values
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{
    let res1: crate::cbordetveraux::cbor_raw = parse_any(c);
    let res2: crate::cbordetveraux::cbor_raw = evercddl_values_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_values
*/
pub fn
serialize_values(c: crate::cbordetveraux::cbor_raw, out: &mut [u8]) ->
    usize
{
    let c·: crate::cbordetveraux::cbor_raw = evercddl_values_pretty_left(c);
    let res: usize = serialize_any(c·, out);
    res
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_values_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (crate::cbordetveraux::cbor_raw <'a>, &'a [u8]) }
}

pub fn validate_and_parse_values <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_values_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_values_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_values(rl);
              if test
              {
                  let x: crate::cbordetveraux::cbor_raw = parse_values(rl);
                  option__·COSE_Format_evercddl_values_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_values_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn aux_env25_validate_1(
    pi: &mut [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw]
) ->
    bool
{
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = pi[0];
    let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i);
    if is_done
    { false }
    else
    {
        let c: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_array_iterator_next(pi);
        let test: bool = validate_label(c);
        test
    }
}

pub type aux_env25_type_1_pretty <'a> = evercddl_label_pretty <'a>;

pub fn uu___is_Mkaux_env25_type_1_pretty0(projectee: evercddl_label_pretty) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_label_pretty>(projectee);
    true
}

fn aux_env25_type_1_pretty_right <'a>(x1: evercddl_label_pretty <'a>) ->
    evercddl_label_pretty
    <'a>
{ x1 }

fn aux_env25_type_1_pretty_left <'a>(x3: evercddl_label_pretty <'a>) ->
    evercddl_label_pretty
    <'a>
{ x3 }

/**
Parser for aux_env25_type_1
*/
pub fn
aux_env25_parse_1
<'a>(c: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>) ->
    evercddl_label_pretty
    <'a>
{
    let mut pc: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c; 1usize];
    let x: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
    let res: evercddl_label_pretty = parse_label(x);
    let res1: evercddl_label_pretty = res;
    let res2: evercddl_label_pretty = aux_env25_type_1_pretty_right(res1);
    res2
}

/**
Serializer for aux_env25_type_1
*/
pub fn
aux_env25_serialize_1(
    c: evercddl_label_pretty,
    out: &mut [u8],
    out_count: &mut [u64],
    out_size: &mut [usize]
) ->
    bool
{
    let c·: evercddl_label_pretty = aux_env25_type_1_pretty_left(c);
    let count: u64 = out_count[0];
    if count < 18446744073709551615u64
    {
        let size: usize = out_size[0];
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
        let _out0: &[u8] = _letpattern.0;
        let out1: &mut [u8] = _letpattern.1;
        let size1: usize = serialize_label(c·, out1);
        if size1 == 0usize
        { false }
        else
        {
            out_count[0] = count.wrapping_add(1u64);
            out_size[0] = size.wrapping_add(size1);
            true
        }
    }
    else
    { false }
}

pub fn aux_env25_validate_2(c: crate::cbordetveraux::cbor_raw) -> bool { validate_label(c) }

pub type aux_env25_type_2_pretty <'a> = evercddl_label_pretty <'a>;

pub fn uu___is_Mkaux_env25_type_2_pretty0(projectee: evercddl_label_pretty) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_label_pretty>(projectee);
    true
}

fn aux_env25_type_2_pretty_right <'a>(x1: evercddl_label_pretty <'a>) ->
    evercddl_label_pretty
    <'a>
{ x1 }

fn aux_env25_type_2_pretty_left <'a>(x3: evercddl_label_pretty <'a>) ->
    evercddl_label_pretty
    <'a>
{ x3 }

/**
Parser for aux_env25_type_2
*/
pub fn
aux_env25_parse_2
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_label_pretty
    <'a>
{
    let res1: evercddl_label_pretty = parse_label(c);
    let res2: evercddl_label_pretty = aux_env25_type_2_pretty_right(res1);
    res2
}

/**
Serializer for aux_env25_type_2
*/
pub fn
aux_env25_serialize_2(c: evercddl_label_pretty, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_label_pretty = aux_env25_type_2_pretty_left(c);
    let res: usize = serialize_label(c·, out);
    res
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_aux_env25_type_2_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_label_pretty <'a>, &'a [u8]) }
}

pub fn validate_and_aux_env25_parse_2 <'a>(s: &'a [u8]) ->
    option__·COSE_Format_aux_env25_type_2_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_aux_env25_type_2_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = aux_env25_validate_2(rl);
              if test
              {
                  let x: evercddl_label_pretty = aux_env25_parse_2(rl);
                  option__·COSE_Format_aux_env25_type_2_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_aux_env25_type_2_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn aux_env25_validate_3(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;
    let test: bool =
        if is_uint
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern: crate::cbordetver::cbor_det_view = v1;
            let i: u64 =
                match _letpattern
                {
                    crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                    _ => panic!("Incomplete pattern matching")
                };
            i == 1u64
        }
        else
        { false };
    let test0: bool =
        if test
        { true }
        else
        {
            let mt0: u8 = crate::cbordetver::cbor_det_major_type(c);
            let is_uint0: bool = mt0 == crate::cbordetveraux::cbor_major_type_uint64;
            if is_uint0
            {
                let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
                let _letpattern: crate::cbordetver::cbor_det_view = v1;
                let i: u64 =
                    match _letpattern
                    {
                        crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                        _ => panic!("Incomplete pattern matching")
                    };
                i == 2u64
            }
            else
            { false }
        };
    let test1: bool =
        if test0
        { true }
        else
        {
            let mt0: u8 = crate::cbordetver::cbor_det_major_type(c);
            let is_uint0: bool = mt0 == crate::cbordetveraux::cbor_major_type_uint64;
            if is_uint0
            {
                let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
                let _letpattern: crate::cbordetver::cbor_det_view = v1;
                let i: u64 =
                    match _letpattern
                    {
                        crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                        _ => panic!("Incomplete pattern matching")
                    };
                i == 3u64
            }
            else
            { false }
        };
    let test2: bool =
        if test1
        { true }
        else
        {
            let mt0: u8 = crate::cbordetver::cbor_det_major_type(c);
            let is_uint0: bool = mt0 == crate::cbordetveraux::cbor_major_type_uint64;
            if is_uint0
            {
                let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
                let _letpattern: crate::cbordetver::cbor_det_view = v1;
                let i: u64 =
                    match _letpattern
                    {
                        crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                        _ => panic!("Incomplete pattern matching")
                    };
                i == 4u64
            }
            else
            { false }
        };
    let test3: bool =
        if test2
        { true }
        else
        {
            let mt0: u8 = crate::cbordetver::cbor_det_major_type(c);
            let is_uint0: bool = mt0 == crate::cbordetveraux::cbor_major_type_uint64;
            if is_uint0
            {
                let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
                let _letpattern: crate::cbordetver::cbor_det_view = v1;
                let i: u64 =
                    match _letpattern
                    {
                        crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                        _ => panic!("Incomplete pattern matching")
                    };
                i == 5u64
            }
            else
            { false }
        };
    if test3
    { true }
    else
    {
        let mt0: u8 = crate::cbordetver::cbor_det_major_type(c);
        let is_uint0: bool = mt0 == crate::cbordetveraux::cbor_major_type_uint64;
        if is_uint0
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern: crate::cbordetver::cbor_det_view = v1;
            let i: u64 =
                match _letpattern
                {
                    crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                    _ => panic!("Incomplete pattern matching")
                };
            i == 6u64
        }
        else
        { false }
    }
}

pub fn aux_env25_validate_4(c: crate::cbordetveraux::cbor_raw) -> bool { validate_values(c) }

pub type aux_env25_type_4_pretty <'a> = evercddl_values_pretty <'a>;

pub fn uu___is_Mkaux_env25_type_4_pretty0(projectee: crate::cbordetveraux::cbor_raw) -> bool
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(projectee);
    true
}

fn aux_env25_type_4_pretty_right <'a>(x1: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x1 }

fn aux_env25_type_4_pretty_left <'a>(x3: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x3 }

/**
Parser for aux_env25_type_4
*/
pub fn
aux_env25_parse_4
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{
    let res1: crate::cbordetveraux::cbor_raw = parse_values(c);
    let res2: crate::cbordetveraux::cbor_raw = aux_env25_type_4_pretty_right(res1);
    res2
}

/**
Serializer for aux_env25_type_4
*/
pub fn
aux_env25_serialize_4(c: crate::cbordetveraux::cbor_raw, out: &mut [u8]) ->
    usize
{
    let c·: crate::cbordetveraux::cbor_raw = aux_env25_type_4_pretty_left(c);
    let res: usize = serialize_values(c·, out);
    res
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_aux_env25_type_4_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (crate::cbordetveraux::cbor_raw <'a>, &'a [u8]) }
}

pub fn validate_and_aux_env25_parse_4 <'a>(s: &'a [u8]) ->
    option__·COSE_Format_aux_env25_type_4_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_aux_env25_type_4_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = aux_env25_validate_4(rl);
              if test
              {
                  let x: crate::cbordetveraux::cbor_raw = aux_env25_parse_4(rl);
                  option__·COSE_Format_aux_env25_type_4_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_aux_env25_type_4_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_header_map(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let ty: u8 = crate::cbordetver::cbor_det_major_type(c);
    if ty == crate::cbordetveraux::cbor_major_type_map
    {
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let rem0: u64 =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Map { _0: a } =>
                  {
                      let res: u64 = crate::cbordetver::cbor_det_map_length(a);
                      res
                  },
                _ => panic!("Incomplete pattern matching")
            };
        let mut remaining: [u64; 1] = [rem0; 1usize];
        let i0: u64 = (&remaining)[0];
        let mty: crate::cbordetver::cbor_det_int_kind =
            crate::cbordetver::cbor_det_int_kind::UInt64;
        let c1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty, 1u64);
        let x·: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern0: crate::cbordetver::cbor_det_view = x·;
        let mg: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
            match _letpattern0
            {
                crate::cbordetver::cbor_det_view::Map { _0: m1 } =>
                  {
                      let res: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                          crate::cbordetver::cbor_det_map_get(m1, c1);
                      res
                  },
                _ => panic!("Incomplete pattern matching")
            };
        let res: crate::cbordetveraux::impl_map_group_result =
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
                          let i1: u64 = (&remaining)[0];
                          let i2: u64 = i1.wrapping_sub(1u64);
                          (&mut remaining)[0] = i2;
                          crate::cbordetveraux::impl_map_group_result::MGOK
                      }
                      else
                      { crate::cbordetveraux::impl_map_group_result::MGCutFail }
                  },
                _ => panic!("Incomplete pattern matching")
            };
        let res0: crate::cbordetveraux::impl_map_group_result = res;
        let res1: crate::cbordetveraux::impl_map_group_result = res0;
        let res10: crate::cbordetveraux::impl_map_group_result =
            match res1
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  crate::cbordetveraux::impl_map_group_result::MGOK,
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  {
                      (&mut remaining)[0] = i0;
                      crate::cbordetveraux::impl_map_group_result::MGOK
                  },
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        let res11: crate::cbordetveraux::impl_map_group_result =
            match res10
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  {
                      let i00: u64 = (&remaining)[0];
                      let mty0: crate::cbordetver::cbor_det_int_kind =
                          crate::cbordetver::cbor_det_int_kind::UInt64;
                      let c10: crate::cbordetveraux::cbor_raw =
                          crate::cbordetver::cbor_det_mk_int64(mty0, 2u64);
                      let x·0: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let _letpattern1: crate::cbordetver::cbor_det_view = x·0;
                      let mg0: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                          match _letpattern1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: m2 } =>
                                {
                                    let
                                    res2: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                    =
                                        crate::cbordetver::cbor_det_map_get(m2, c10);
                                    res2
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res2: crate::cbordetveraux::impl_map_group_result =
                          match mg0
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
                                            let v10: crate::cbordetver::cbor_det_view =
                                                crate::cbordetver::cbor_det_destruct(cv);
                                            let _letpattern2: crate::cbordetver::cbor_det_view =
                                                v10;
                                            let
                                            i:
                                            crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                            =
                                                match _letpattern2
                                                {
                                                    crate::cbordetver::cbor_det_view::Array
                                                    { _0: a }
                                                    =>
                                                      {
                                                          let
                                                          res2:
                                                          crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                          =
                                                              crate::cbordetver::cbor_det_array_iterator_start(
                                                                  a
                                                              );
                                                          res2
                                                      },
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
                                                (&pi)[0];
                                            let is_done: bool =
                                                crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                    i1
                                                );
                                            let test1: bool =
                                                if is_done
                                                { false }
                                                else
                                                {
                                                    let c2: crate::cbordetveraux::cbor_raw =
                                                        crate::cbordetver::cbor_det_array_iterator_next(
                                                            &mut pi
                                                        );
                                                    let test: bool = validate_label(c2);
                                                    test
                                                };
                                            let b_success: bool =
                                                if test1
                                                {
                                                    let mut pcont: [bool; 1] = [true; 1usize];
                                                    while
                                                    (&pcont)[0]
                                                    {
                                                        let
                                                        i10:
                                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                        =
                                                            (&pi)[0];
                                                        let
                                                        i2:
                                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                        =
                                                            (&pi)[0];
                                                        let is_done0: bool =
                                                            crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                                i2
                                                            );
                                                        let cont: bool =
                                                            if is_done0
                                                            { false }
                                                            else
                                                            {
                                                                let
                                                                c2: crate::cbordetveraux::cbor_raw
                                                                =
                                                                    crate::cbordetver::cbor_det_array_iterator_next(
                                                                        &mut pi
                                                                    );
                                                                let test: bool = validate_label(c2);
                                                                test
                                                            };
                                                        if ! cont
                                                        {
                                                            (&mut pi)[0] = i10;
                                                            (&mut pcont)[0] = false
                                                        }
                                                    };
                                                    let test2: bool = true;
                                                    test2
                                                }
                                                else
                                                { false };
                                            let _bind_c: bool =
                                                if b_success
                                                {
                                                    let
                                                    i·:
                                                    crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                    =
                                                        (&pi)[0];
                                                    let b_end: bool =
                                                        crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                            i·
                                                        );
                                                    b_end
                                                }
                                                else
                                                { false };
                                            _bind_c
                                        }
                                        else
                                        { false };
                                    if check_value
                                    {
                                        let i1: u64 = (&remaining)[0];
                                        let i2: u64 = i1.wrapping_sub(1u64);
                                        (&mut remaining)[0] = i2;
                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                    }
                                    else
                                    { crate::cbordetveraux::impl_map_group_result::MGCutFail }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res3: crate::cbordetveraux::impl_map_group_result = res2;
                      let res11: crate::cbordetveraux::impl_map_group_result = res3;
                      let res4: crate::cbordetveraux::impl_map_group_result =
                          match res11
                          {
                              crate::cbordetveraux::impl_map_group_result::MGOK =>
                                crate::cbordetveraux::impl_map_group_result::MGOK,
                              crate::cbordetveraux::impl_map_group_result::MGFail =>
                                {
                                    (&mut remaining)[0] = i00;
                                    crate::cbordetveraux::impl_map_group_result::MGOK
                                },
                              crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                                crate::cbordetveraux::impl_map_group_result::MGCutFail,
                              _ => panic!("Precondition of the function most likely violated")
                          };
                      res4
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
                      let i00: u64 = (&remaining)[0];
                      let mty0: crate::cbordetver::cbor_det_int_kind =
                          crate::cbordetver::cbor_det_int_kind::UInt64;
                      let c10: crate::cbordetveraux::cbor_raw =
                          crate::cbordetver::cbor_det_mk_int64(mty0, 3u64);
                      let x·0: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let _letpattern1: crate::cbordetver::cbor_det_view = x·0;
                      let mg0: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                          match _letpattern1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: m2 } =>
                                {
                                    let
                                    res2: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                    =
                                        crate::cbordetver::cbor_det_map_get(m2, c10);
                                    res2
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res2: crate::cbordetveraux::impl_map_group_result =
                          match mg0
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
                                        let i1: u64 = (&remaining)[0];
                                        let i2: u64 = i1.wrapping_sub(1u64);
                                        (&mut remaining)[0] = i2;
                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                    }
                                    else
                                    { crate::cbordetveraux::impl_map_group_result::MGCutFail }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res3: crate::cbordetveraux::impl_map_group_result = res2;
                      let res110: crate::cbordetveraux::impl_map_group_result = res3;
                      let res4: crate::cbordetveraux::impl_map_group_result =
                          match res110
                          {
                              crate::cbordetveraux::impl_map_group_result::MGOK =>
                                crate::cbordetveraux::impl_map_group_result::MGOK,
                              crate::cbordetveraux::impl_map_group_result::MGFail =>
                                {
                                    (&mut remaining)[0] = i00;
                                    crate::cbordetveraux::impl_map_group_result::MGOK
                                },
                              crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                                crate::cbordetveraux::impl_map_group_result::MGCutFail,
                              _ => panic!("Precondition of the function most likely violated")
                          };
                      res4
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
                      let i00: u64 = (&remaining)[0];
                      let mty0: crate::cbordetver::cbor_det_int_kind =
                          crate::cbordetver::cbor_det_int_kind::UInt64;
                      let c10: crate::cbordetveraux::cbor_raw =
                          crate::cbordetver::cbor_det_mk_int64(mty0, 4u64);
                      let x·0: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let _letpattern1: crate::cbordetver::cbor_det_view = x·0;
                      let mg0: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                          match _letpattern1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: m2 } =>
                                {
                                    let
                                    res2: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                    =
                                        crate::cbordetver::cbor_det_map_get(m2, c10);
                                    res2
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res2: crate::cbordetveraux::impl_map_group_result =
                          match mg0
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
                                        let i1: u64 = (&remaining)[0];
                                        let i2: u64 = i1.wrapping_sub(1u64);
                                        (&mut remaining)[0] = i2;
                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                    }
                                    else
                                    { crate::cbordetveraux::impl_map_group_result::MGCutFail }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res3: crate::cbordetveraux::impl_map_group_result = res2;
                      let res110: crate::cbordetveraux::impl_map_group_result = res3;
                      let res4: crate::cbordetveraux::impl_map_group_result =
                          match res110
                          {
                              crate::cbordetveraux::impl_map_group_result::MGOK =>
                                crate::cbordetveraux::impl_map_group_result::MGOK,
                              crate::cbordetveraux::impl_map_group_result::MGFail =>
                                {
                                    (&mut remaining)[0] = i00;
                                    crate::cbordetveraux::impl_map_group_result::MGOK
                                },
                              crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                                crate::cbordetveraux::impl_map_group_result::MGCutFail,
                              _ => panic!("Precondition of the function most likely violated")
                          };
                      res4
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
                      let i00: u64 = (&remaining)[0];
                      let mty0: crate::cbordetver::cbor_det_int_kind =
                          crate::cbordetver::cbor_det_int_kind::UInt64;
                      let c10: crate::cbordetveraux::cbor_raw =
                          crate::cbordetver::cbor_det_mk_int64(mty0, 5u64);
                      let x·0: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let _letpattern1: crate::cbordetver::cbor_det_view = x·0;
                      let mg0: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                          match _letpattern1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: m2 } =>
                                {
                                    let
                                    res2: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                    =
                                        crate::cbordetver::cbor_det_map_get(m2, c10);
                                    res2
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res2: crate::cbordetveraux::impl_map_group_result =
                          match mg0
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
                                        let i1: u64 = (&remaining)[0];
                                        let i2: u64 = i1.wrapping_sub(1u64);
                                        (&mut remaining)[0] = i2;
                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                    }
                                    else
                                    { crate::cbordetveraux::impl_map_group_result::MGFail }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res3: crate::cbordetveraux::impl_map_group_result = res2;
                      let res110: crate::cbordetveraux::impl_map_group_result = res3;
                      let res111: crate::cbordetveraux::impl_map_group_result =
                          match res110
                          {
                              crate::cbordetveraux::impl_map_group_result::MGOK =>
                                {
                                    let i01: u64 = (&remaining)[0];
                                    let mty1: crate::cbordetver::cbor_det_int_kind =
                                        crate::cbordetver::cbor_det_int_kind::UInt64;
                                    let c11: crate::cbordetveraux::cbor_raw =
                                        crate::cbordetver::cbor_det_mk_int64(mty1, 6u64);
                                    let x·1: crate::cbordetver::cbor_det_view =
                                        crate::cbordetver::cbor_det_destruct(c);
                                    let _letpattern2: crate::cbordetver::cbor_det_view = x·1;
                                    let
                                    mg1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                    =
                                        match _letpattern2
                                        {
                                            crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
                                              {
                                                  let
                                                  res4:
                                                  crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                  =
                                                      crate::cbordetver::cbor_det_map_get(m3, c11);
                                                  res4
                                              },
                                            _ => panic!("Incomplete pattern matching")
                                        };
                                    let res4: crate::cbordetveraux::impl_map_group_result =
                                        match mg1
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
                                                      let i1: u64 = (&remaining)[0];
                                                      let i2: u64 = i1.wrapping_sub(1u64);
                                                      (&mut remaining)[0] = i2;
                                                      crate::cbordetveraux::impl_map_group_result::MGOK
                                                  }
                                                  else
                                                  {
                                                      crate::cbordetveraux::impl_map_group_result::MGCutFail
                                                  }
                                              },
                                            _ => panic!("Incomplete pattern matching")
                                        };
                                    let res5: crate::cbordetveraux::impl_map_group_result = res4;
                                    let res120: crate::cbordetveraux::impl_map_group_result = res5;
                                    let res6: crate::cbordetveraux::impl_map_group_result =
                                        match res120
                                        {
                                            crate::cbordetveraux::impl_map_group_result::MGOK =>
                                              crate::cbordetveraux::impl_map_group_result::MGOK,
                                            crate::cbordetveraux::impl_map_group_result::MGFail =>
                                              {
                                                  (&mut remaining)[0] = i01;
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
                                    res6
                                },
                              crate::cbordetveraux::impl_map_group_result::MGFail =>
                                crate::cbordetveraux::impl_map_group_result::MGFail,
                              crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                                crate::cbordetveraux::impl_map_group_result::MGCutFail,
                              _ => panic!("Precondition of the function most likely violated")
                          };
                      let res4: crate::cbordetveraux::impl_map_group_result =
                          match res111
                          {
                              crate::cbordetveraux::impl_map_group_result::MGOK =>
                                crate::cbordetveraux::impl_map_group_result::MGOK,
                              crate::cbordetveraux::impl_map_group_result::MGFail =>
                                {
                                    (&mut remaining)[0] = i00;
                                    let i01: u64 = (&remaining)[0];
                                    let mty1: crate::cbordetver::cbor_det_int_kind =
                                        crate::cbordetver::cbor_det_int_kind::UInt64;
                                    let c11: crate::cbordetveraux::cbor_raw =
                                        crate::cbordetver::cbor_det_mk_int64(mty1, 6u64);
                                    let x·1: crate::cbordetver::cbor_det_view =
                                        crate::cbordetver::cbor_det_destruct(c);
                                    let _letpattern2: crate::cbordetver::cbor_det_view = x·1;
                                    let
                                    mg1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                    =
                                        match _letpattern2
                                        {
                                            crate::cbordetver::cbor_det_view::Map { _0: m2 } =>
                                              {
                                                  let
                                                  res4:
                                                  crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                  =
                                                      crate::cbordetver::cbor_det_map_get(m2, c11);
                                                  res4
                                              },
                                            _ => panic!("Incomplete pattern matching")
                                        };
                                    let res4: crate::cbordetveraux::impl_map_group_result =
                                        match mg1
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
                                                      let i1: u64 = (&remaining)[0];
                                                      let i2: u64 = i1.wrapping_sub(1u64);
                                                      (&mut remaining)[0] = i2;
                                                      crate::cbordetveraux::impl_map_group_result::MGOK
                                                  }
                                                  else
                                                  {
                                                      crate::cbordetveraux::impl_map_group_result::MGFail
                                                  }
                                              },
                                            _ => panic!("Incomplete pattern matching")
                                        };
                                    let res5: crate::cbordetveraux::impl_map_group_result = res4;
                                    let res120: crate::cbordetveraux::impl_map_group_result = res5;
                                    let res121: crate::cbordetveraux::impl_map_group_result =
                                        match res120
                                        {
                                            crate::cbordetveraux::impl_map_group_result::MGOK =>
                                              {
                                                  let i02: u64 = (&remaining)[0];
                                                  let mty2: crate::cbordetver::cbor_det_int_kind =
                                                      crate::cbordetver::cbor_det_int_kind::UInt64;
                                                  let c12: crate::cbordetveraux::cbor_raw =
                                                      crate::cbordetver::cbor_det_mk_int64(
                                                          mty2,
                                                          5u64
                                                      );
                                                  let x·2: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(c);
                                                  let
                                                  _letpattern3: crate::cbordetver::cbor_det_view
                                                  =
                                                      x·2;
                                                  let
                                                  mg2:
                                                  crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                  =
                                                      match _letpattern3
                                                      {
                                                          crate::cbordetver::cbor_det_view::Map
                                                          { _0: m3 }
                                                          =>
                                                            {
                                                                let
                                                                res6:
                                                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                                =
                                                                    crate::cbordetver::cbor_det_map_get(
                                                                        m3,
                                                                        c12
                                                                    );
                                                                res6
                                                            },
                                                          _ => panic!("Incomplete pattern matching")
                                                      };
                                                  let
                                                  res6: crate::cbordetveraux::impl_map_group_result
                                                  =
                                                      match mg2
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
                                                                    let i1: u64 = (&remaining)[0];
                                                                    let i2: u64 =
                                                                        i1.wrapping_sub(1u64);
                                                                    (&mut remaining)[0] = i2;
                                                                    crate::cbordetveraux::impl_map_group_result::MGOK
                                                                }
                                                                else
                                                                {
                                                                    crate::cbordetveraux::impl_map_group_result::MGCutFail
                                                                }
                                                            },
                                                          _ => panic!("Incomplete pattern matching")
                                                      };
                                                  let
                                                  res7: crate::cbordetveraux::impl_map_group_result
                                                  =
                                                      res6;
                                                  let
                                                  res130:
                                                  crate::cbordetveraux::impl_map_group_result
                                                  =
                                                      res7;
                                                  let
                                                  res8: crate::cbordetveraux::impl_map_group_result
                                                  =
                                                      match res130
                                                      {
                                                          crate::cbordetveraux::impl_map_group_result::MGOK
                                                          =>
                                                            crate::cbordetveraux::impl_map_group_result::MGOK,
                                                          crate::cbordetveraux::impl_map_group_result::MGFail
                                                          =>
                                                            {
                                                                (&mut remaining)[0] = i02;
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
                                                  res8
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
                                        };
                                    let res6: crate::cbordetveraux::impl_map_group_result =
                                        match res121
                                        {
                                            crate::cbordetveraux::impl_map_group_result::MGOK =>
                                              crate::cbordetveraux::impl_map_group_result::MGOK,
                                            crate::cbordetveraux::impl_map_group_result::MGFail =>
                                              {
                                                  (&mut remaining)[0] = i01;
                                                  let i02: u64 = (&remaining)[0];
                                                  let mty2: crate::cbordetver::cbor_det_int_kind =
                                                      crate::cbordetver::cbor_det_int_kind::UInt64;
                                                  let c12: crate::cbordetveraux::cbor_raw =
                                                      crate::cbordetver::cbor_det_mk_int64(
                                                          mty2,
                                                          6u64
                                                      );
                                                  let x·2: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(c);
                                                  let
                                                  _letpattern3: crate::cbordetver::cbor_det_view
                                                  =
                                                      x·2;
                                                  let
                                                  mg2:
                                                  crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                  =
                                                      match _letpattern3
                                                      {
                                                          crate::cbordetver::cbor_det_view::Map
                                                          { _0: m2 }
                                                          =>
                                                            {
                                                                let
                                                                res6:
                                                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                                =
                                                                    crate::cbordetver::cbor_det_map_get(
                                                                        m2,
                                                                        c12
                                                                    );
                                                                res6
                                                            },
                                                          _ => panic!("Incomplete pattern matching")
                                                      };
                                                  let
                                                  res6: crate::cbordetveraux::impl_map_group_result
                                                  =
                                                      match mg2
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
                                                                    let i1: u64 = (&remaining)[0];
                                                                    let i2: u64 =
                                                                        i1.wrapping_sub(1u64);
                                                                    (&mut remaining)[0] = i2;
                                                                    crate::cbordetveraux::impl_map_group_result::MGOK
                                                                }
                                                                else
                                                                {
                                                                    crate::cbordetveraux::impl_map_group_result::MGCutFail
                                                                }
                                                            },
                                                          _ => panic!("Incomplete pattern matching")
                                                      };
                                                  let
                                                  res7: crate::cbordetveraux::impl_map_group_result
                                                  =
                                                      res6;
                                                  let
                                                  res130:
                                                  crate::cbordetveraux::impl_map_group_result
                                                  =
                                                      res7;
                                                  let
                                                  res131:
                                                  crate::cbordetveraux::impl_map_group_result
                                                  =
                                                      match res130
                                                      {
                                                          crate::cbordetveraux::impl_map_group_result::MGOK
                                                          =>
                                                            crate::cbordetveraux::impl_map_group_result::MGOK,
                                                          crate::cbordetveraux::impl_map_group_result::MGFail
                                                          =>
                                                            {
                                                                (&mut remaining)[0] = i02;
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
                                                  let
                                                  res8: crate::cbordetveraux::impl_map_group_result
                                                  =
                                                      match res131
                                                      {
                                                          crate::cbordetveraux::impl_map_group_result::MGOK
                                                          =>
                                                            {
                                                                let i020: u64 = (&remaining)[0];
                                                                let
                                                                mty3:
                                                                crate::cbordetver::cbor_det_int_kind
                                                                =
                                                                    crate::cbordetver::cbor_det_int_kind::UInt64;
                                                                let
                                                                c13: crate::cbordetveraux::cbor_raw
                                                                =
                                                                    crate::cbordetver::cbor_det_mk_int64(
                                                                        mty3,
                                                                        5u64
                                                                    );
                                                                let
                                                                x·3:
                                                                crate::cbordetver::cbor_det_view
                                                                =
                                                                    crate::cbordetver::cbor_det_destruct(
                                                                        c
                                                                    );
                                                                let
                                                                _letpattern4:
                                                                crate::cbordetver::cbor_det_view
                                                                =
                                                                    x·3;
                                                                let
                                                                mg3:
                                                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                                =
                                                                    match _letpattern4
                                                                    {
                                                                        crate::cbordetver::cbor_det_view::Map
                                                                        { _0: m3 }
                                                                        =>
                                                                          {
                                                                              let
                                                                              res8:
                                                                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                                              =
                                                                                  crate::cbordetver::cbor_det_map_get(
                                                                                      m3,
                                                                                      c13
                                                                                  );
                                                                              res8
                                                                          },
                                                                        _ =>
                                                                          panic!(
                                                                              "Incomplete pattern matching"
                                                                          )
                                                                    };
                                                                let
                                                                res8:
                                                                crate::cbordetveraux::impl_map_group_result
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
                                                                              let
                                                                              check_value: bool
                                                                              =
                                                                                  validate_everparsenomatch(
                                                                                      cv
                                                                                  );
                                                                              if check_value
                                                                              {
                                                                                  let i1: u64 =
                                                                                      (&remaining)[0];
                                                                                  let i2: u64 =
                                                                                      i1.wrapping_sub(
                                                                                          1u64
                                                                                      );
                                                                                  (&mut remaining)[0] =
                                                                                      i2;
                                                                                  crate::cbordetveraux::impl_map_group_result::MGOK
                                                                              }
                                                                              else
                                                                              {
                                                                                  crate::cbordetveraux::impl_map_group_result::MGCutFail
                                                                              }
                                                                          },
                                                                        _ =>
                                                                          panic!(
                                                                              "Incomplete pattern matching"
                                                                          )
                                                                    };
                                                                let
                                                                res9:
                                                                crate::cbordetveraux::impl_map_group_result
                                                                =
                                                                    res8;
                                                                let
                                                                res14:
                                                                crate::cbordetveraux::impl_map_group_result
                                                                =
                                                                    res9;
                                                                let
                                                                res15:
                                                                crate::cbordetveraux::impl_map_group_result
                                                                =
                                                                    match res14
                                                                    {
                                                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                                                        =>
                                                                          crate::cbordetveraux::impl_map_group_result::MGOK,
                                                                        crate::cbordetveraux::impl_map_group_result::MGFail
                                                                        =>
                                                                          {
                                                                              (&mut remaining)[0] =
                                                                                  i020;
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
                                                                res15
                                                            },
                                                          crate::cbordetveraux::impl_map_group_result::MGFail
                                                          =>
                                                            crate::cbordetveraux::impl_map_group_result::MGFail,
                                                          crate::cbordetveraux::impl_map_group_result::MGCutFail
                                                          =>
                                                            crate::cbordetveraux::impl_map_group_result::MGCutFail,
                                                          _ =>
                                                            panic!(
                                                                "Precondition of the function most likely violated"
                                                            )
                                                      };
                                                  res8
                                              },
                                            crate::cbordetveraux::impl_map_group_result::MGCutFail
                                            =>
                                              crate::cbordetveraux::impl_map_group_result::MGCutFail,
                                            _ =>
                                              panic!(
                                                  "Precondition of the function most likely violated"
                                              )
                                        };
                                    res6
                                },
                              crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                                crate::cbordetveraux::impl_map_group_result::MGCutFail,
                              _ => panic!("Precondition of the function most likely violated")
                          };
                      res4
                  },
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        let res2: crate::cbordetveraux::impl_map_group_result =
            match res14
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  {
                      let v10: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let _letpattern1: crate::cbordetver::cbor_det_view = v10;
                      let
                      j0:
                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                      =
                          match _letpattern1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: a } =>
                                {
                                    let
                                    res2:
                                    crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                    =
                                        crate::cbordetver::cbor_det_map_iterator_start(a);
                                    res2
                                },
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
                          (&pj)[0];
                      let is_empty: bool = crate::cbordetver::cbor_det_map_iterator_is_empty(j);
                      let mut cond: bool = ! is_empty;
                      while
                      cond
                      {
                          let chd: crate::cbordetveraux::cbor_map_entry =
                              crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
                          let k: crate::cbordetveraux::cbor_raw =
                              crate::cbordetver::cbor_det_map_entry_key(chd);
                          let test1: bool = validate_label(k);
                          let testk: bool =
                              if test1
                              {
                                  let mt: u8 = crate::cbordetver::cbor_det_major_type(k);
                                  let is_uint: bool =
                                      mt == crate::cbordetveraux::cbor_major_type_uint64;
                                  let test: bool =
                                      if is_uint
                                      {
                                          let v11: crate::cbordetver::cbor_det_view =
                                              crate::cbordetver::cbor_det_destruct(k);
                                          let _letpattern2: crate::cbordetver::cbor_det_view = v11;
                                          let i: u64 =
                                              match _letpattern2
                                              {
                                                  crate::cbordetver::cbor_det_view::Int64
                                                  { value: res2, .. }
                                                  => res2,
                                                  _ => panic!("Incomplete pattern matching")
                                              };
                                          i == 1u64
                                      }
                                      else
                                      { false };
                                  let test0: bool =
                                      if test
                                      { true }
                                      else
                                      {
                                          let mt0: u8 = crate::cbordetver::cbor_det_major_type(k);
                                          let is_uint0: bool =
                                              mt0 == crate::cbordetveraux::cbor_major_type_uint64;
                                          if is_uint0
                                          {
                                              let v11: crate::cbordetver::cbor_det_view =
                                                  crate::cbordetver::cbor_det_destruct(k);
                                              let _letpattern2: crate::cbordetver::cbor_det_view =
                                                  v11;
                                              let i: u64 =
                                                  match _letpattern2
                                                  {
                                                      crate::cbordetver::cbor_det_view::Int64
                                                      { value: res2, .. }
                                                      => res2,
                                                      _ => panic!("Incomplete pattern matching")
                                                  };
                                              i == 2u64
                                          }
                                          else
                                          { false }
                                      };
                                  let test2: bool =
                                      if test0
                                      { true }
                                      else
                                      {
                                          let mt0: u8 = crate::cbordetver::cbor_det_major_type(k);
                                          let is_uint0: bool =
                                              mt0 == crate::cbordetveraux::cbor_major_type_uint64;
                                          if is_uint0
                                          {
                                              let v11: crate::cbordetver::cbor_det_view =
                                                  crate::cbordetver::cbor_det_destruct(k);
                                              let _letpattern2: crate::cbordetver::cbor_det_view =
                                                  v11;
                                              let i: u64 =
                                                  match _letpattern2
                                                  {
                                                      crate::cbordetver::cbor_det_view::Int64
                                                      { value: res2, .. }
                                                      => res2,
                                                      _ => panic!("Incomplete pattern matching")
                                                  };
                                              i == 3u64
                                          }
                                          else
                                          { false }
                                      };
                                  let test3: bool =
                                      if test2
                                      { true }
                                      else
                                      {
                                          let mt0: u8 = crate::cbordetver::cbor_det_major_type(k);
                                          let is_uint0: bool =
                                              mt0 == crate::cbordetveraux::cbor_major_type_uint64;
                                          if is_uint0
                                          {
                                              let v11: crate::cbordetver::cbor_det_view =
                                                  crate::cbordetver::cbor_det_destruct(k);
                                              let _letpattern2: crate::cbordetver::cbor_det_view =
                                                  v11;
                                              let i: u64 =
                                                  match _letpattern2
                                                  {
                                                      crate::cbordetver::cbor_det_view::Int64
                                                      { value: res2, .. }
                                                      => res2,
                                                      _ => panic!("Incomplete pattern matching")
                                                  };
                                              i == 4u64
                                          }
                                          else
                                          { false }
                                      };
                                  let test4: bool =
                                      if test3
                                      { true }
                                      else
                                      {
                                          let mt0: u8 = crate::cbordetver::cbor_det_major_type(k);
                                          let is_uint0: bool =
                                              mt0 == crate::cbordetveraux::cbor_major_type_uint64;
                                          if is_uint0
                                          {
                                              let v11: crate::cbordetver::cbor_det_view =
                                                  crate::cbordetver::cbor_det_destruct(k);
                                              let _letpattern2: crate::cbordetver::cbor_det_view =
                                                  v11;
                                              let i: u64 =
                                                  match _letpattern2
                                                  {
                                                      crate::cbordetver::cbor_det_view::Int64
                                                      { value: res2, .. }
                                                      => res2,
                                                      _ => panic!("Incomplete pattern matching")
                                                  };
                                              i == 5u64
                                          }
                                          else
                                          { false }
                                      };
                                  let test5: bool =
                                      if test4
                                      { true }
                                      else
                                      {
                                          let mt0: u8 = crate::cbordetver::cbor_det_major_type(k);
                                          let is_uint0: bool =
                                              mt0 == crate::cbordetveraux::cbor_major_type_uint64;
                                          if is_uint0
                                          {
                                              let v11: crate::cbordetver::cbor_det_view =
                                                  crate::cbordetver::cbor_det_destruct(k);
                                              let _letpattern2: crate::cbordetver::cbor_det_view =
                                                  v11;
                                              let i: u64 =
                                                  match _letpattern2
                                                  {
                                                      crate::cbordetver::cbor_det_view::Int64
                                                      { value: res2, .. }
                                                      => res2,
                                                      _ => panic!("Incomplete pattern matching")
                                                  };
                                              i == 6u64
                                          }
                                          else
                                          { false }
                                      };
                                  ! test5
                              }
                              else
                              { false };
                          let test: bool =
                              if testk
                              {
                                  let v11: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_value(chd);
                                  let testv: bool = validate_values(v11);
                                  testv
                              }
                              else
                              { false };
                          let test0: bool = ! test;
                          if ! test0
                          {
                              let i: u64 = (&remaining)[0];
                              let i·: u64 = i.wrapping_sub(1u64);
                              (&mut remaining)[0] = i·
                          };
                          let
                          j1:
                          crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                          =
                              (&pj)[0];
                          let is_empty0: bool =
                              crate::cbordetver::cbor_det_map_iterator_is_empty(j1);
                          cond = ! is_empty0
                      };
                      let res2: crate::cbordetveraux::impl_map_group_result =
                          crate::cbordetveraux::impl_map_group_result::MGOK;
                      res2
                  },
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        match res2
        {
            crate::cbordetveraux::impl_map_group_result::MGOK =>
              {
                  let rem: u64 = (&remaining)[0];
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
pub enum
option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty
<'a>
{
    None,
    Some { v: evercddl_label <'a> }
}

#[derive(PartialEq, Clone, Copy)]
pub struct
array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env25_type_1_pretty
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
    evercddl_label_pretty
    <'a1>
}

#[derive(PartialEq, Clone, Copy)]
pub enum
either__CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty
<'a>
{
    Inl { v: &'a [evercddl_label_pretty <'a>] },
    Inr
    {
        v:
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env25_type_1_pretty
        <'a>
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty
<'a>
{
    None,
    Some
    {
        v:
        either__CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty
        <'a>
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty <'a>
{
    Inl { v: &'a [u8] },
    Inr { v: evercddl_int_pretty }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty
<'a>
{
    None,
    Some { v: either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty <'a> }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__COSE_Format_evercddl_bstr_pretty <'a>
{
    None,
    Some { v: &'a [u8] }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__COSE_Format_evercddl_everparsenomatch_pretty
{
    None,
    Some { v: evercddl_everparsenomatch_pretty }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_·FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·
<'a>
{
    Inl { v: (&'a [u8], option__COSE_Format_evercddl_everparsenomatch_pretty) },
    Inr
    {
        v:
        (option__COSE_Format_evercddl_everparsenomatch_pretty,
        option__COSE_Format_evercddl_everparsenomatch_pretty)
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_FStar_Pervasives_either··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·
<'a>
{
    Inl { v: (&'a [u8], option__COSE_Format_evercddl_everparsenomatch_pretty) },
    Inr
    {
        v:
        either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_·FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·
        <'a>
    }
}

#[derive(PartialEq, Clone, Copy)]
pub struct
map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
<'a>
{
    pub cddl_map_iterator_contents:
    crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>,
    pub cddl_map_iterator_impl_validate1: fn (crate::cbordetveraux::cbor_raw) -> bool,
    pub cddl_map_iterator_impl_parse1:
    for<'a1> fn (crate::cbordetveraux::cbor_raw <'a1>) -> evercddl_label_pretty <'a1>,
    pub cddl_map_iterator_impl_validate_ex: fn (crate::cbordetveraux::cbor_raw) -> bool,
    pub cddl_map_iterator_impl_validate2: fn (crate::cbordetveraux::cbor_raw) -> bool,
    pub cddl_map_iterator_impl_parse2:
    for<'a1> fn (crate::cbordetveraux::cbor_raw <'a1>) -> crate::cbordetveraux::cbor_raw <'a1>
}

#[derive(PartialEq, Clone, Copy)]
pub enum
either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty
<'a>
{
    Inl { v: &'a [(evercddl_label_pretty <'a>, crate::cbordetveraux::cbor_raw <'a>)] },
    Inr
    {
        v:
        map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
        <'a>
    }
}

#[derive(PartialEq, Clone, Copy)]
pub struct evercddl_header_map_pretty <'a>
{
    pub intkey1:
    option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty
    <'a>,
    pub intkey2:
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty
    <'a>,
    pub intkey3:
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty
    <'a>,
    pub intkey4: option__COSE_Format_evercddl_bstr_pretty <'a>,
    pub _x0:
    either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_FStar_Pervasives_either··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·
    <'a>,
    pub _x1:
    either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty
    <'a>
}

pub fn uu___is_Mkevercddl_header_map_pretty0(projectee: evercddl_header_map_pretty) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_header_map_pretty>(projectee);
    true
}

fn evercddl_header_map_pretty_right <'a>(
    x6:
    (((((option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty
    <'a>,
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty
    <'a>),
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty
    <'a>),
    option__COSE_Format_evercddl_bstr_pretty
    <'a>),
    either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_FStar_Pervasives_either··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·
    <'a>),
    either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty
    <'a>)
) ->
    evercddl_header_map_pretty
    <'a>
{
    match x6
    {
        (((((x7,x8),x9),x10),x11),x12) =>
          evercddl_header_map_pretty
          { intkey1: x7, intkey2: x8, intkey3: x9, intkey4: x10, _x0: x11, _x1: x12 }
    }
}

fn evercddl_header_map_pretty_left <'a>(x13: evercddl_header_map_pretty <'a>) ->
    (((((option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty
    <'a>,
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty
    <'a>),
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty
    <'a>),
    option__COSE_Format_evercddl_bstr_pretty
    <'a>),
    either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_FStar_Pervasives_either··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·
    <'a>),
    either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty
    <'a>)
{
    let
    x21:
    option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty
    =
        x13.intkey1;
    let
    x22:
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty
    =
        x13.intkey2;
    let
    x23:
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty
    =
        x13.intkey3;
    let x24: option__COSE_Format_evercddl_bstr_pretty = x13.intkey4;
    let
    x25:
    either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_FStar_Pervasives_either··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·
    =
        x13._x0;
    let
    x26:
    either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty
    =
        x13._x1;
    (((((x21,x22),x23),x24),x25),x26)
}

/**
Parser for evercddl_header_map
*/
pub fn
parse_header_map
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_header_map_pretty
    <'a>
{
    let dummy: [u64; 1] = [0u64; 1usize];
    crate::lowstar::ignore::ignore::<&[u64]>(&dummy);
    let mty: crate::cbordetver::cbor_det_int_kind = crate::cbordetver::cbor_det_int_kind::UInt64;
    let c1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty, 1u64);
    let x·: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = x·;
    let mg: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
              {
                  let res: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                      crate::cbordetver::cbor_det_map_get(m3, c1);
                  res
              },
            _ => panic!("Incomplete pattern matching")
        };
    let res: crate::cbordetveraux::impl_map_group_result =
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
                  { crate::cbordetveraux::impl_map_group_result::MGCutFail }
              },
            _ => panic!("Incomplete pattern matching")
        };
    let res0: crate::cbordetveraux::impl_map_group_result = res;
    let test1: crate::cbordetveraux::impl_map_group_result = res0;
    let
    _bind_c:
    option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty
    =
        if crate::cbordetveraux::uu___is_MGOK(test1)
        {
            let mty0: crate::cbordetver::cbor_det_int_kind =
                crate::cbordetver::cbor_det_int_kind::UInt64;
            let c10: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty0, 1u64);
            let x·0: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern0: crate::cbordetver::cbor_det_view = x·0;
            let ow: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match _letpattern0
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
                      {
                          let res1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                              crate::cbordetver::cbor_det_map_get(m3, c10);
                          res1
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            let _letpattern1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow;
            let res1: evercddl_label =
                match _letpattern1
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      {
                          let test: bool = validate_int(w);
                          let res1: evercddl_label =
                              if test
                              {
                                  let res1: evercddl_int_pretty = parse_int(w);
                                  evercddl_label::Inl { v: res1 }
                              }
                              else
                              {
                                  let res1: &[u8] = parse_tstr(w);
                                  evercddl_label::Inr { v: res1 }
                              };
                          res1
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            let w1: evercddl_label = res1;
            option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty::Some
            { v: w1 }
        }
        else
        {
            option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty::None
        };
    let
    w1:
    option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty
    =
        _bind_c;
    let dummy0: [u64; 1] = [0u64; 1usize];
    crate::lowstar::ignore::ignore::<&[u64]>(&dummy0);
    let mty0: crate::cbordetver::cbor_det_int_kind = crate::cbordetver::cbor_det_int_kind::UInt64;
    let c10: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty0, 2u64);
    let x·0: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern0: crate::cbordetver::cbor_det_view = x·0;
    let mg0: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern0
        {
            crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
              {
                  let res1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                      crate::cbordetver::cbor_det_map_get(m3, c10);
                  res1
              },
            _ => panic!("Incomplete pattern matching")
        };
    let res1: crate::cbordetveraux::impl_map_group_result =
        match mg0
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
              crate::cbordetveraux::impl_map_group_result::MGFail,
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: cv } =>
              {
                  let ty: u8 = crate::cbordetver::cbor_det_major_type(cv);
                  let check_value: bool =
                      if ty == crate::cbordetveraux::cbor_major_type_array
                      {
                          let v1: crate::cbordetver::cbor_det_view =
                              crate::cbordetver::cbor_det_destruct(cv);
                          let _letpattern1: crate::cbordetver::cbor_det_view = v1;
                          let
                          i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                          =
                              match _letpattern1
                              {
                                  crate::cbordetver::cbor_det_view::Array { _0: a } =>
                                    {
                                        let
                                        res1:
                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                        =
                                            crate::cbordetver::cbor_det_array_iterator_start(a);
                                        res1
                                    },
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
                              (&pi)[0];
                          let is_done: bool =
                              crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
                          let test10: bool =
                              if is_done
                              { false }
                              else
                              {
                                  let c2: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                  let test: bool = validate_label(c2);
                                  test
                              };
                          let b_success: bool =
                              if test10
                              {
                                  let mut pcont: [bool; 1] = [true; 1usize];
                                  while
                                  (&pcont)[0]
                                  {
                                      let
                                      i10:
                                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                      =
                                          (&pi)[0];
                                      let
                                      i2:
                                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                      =
                                          (&pi)[0];
                                      let is_done0: bool =
                                          crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
                                      let cont: bool =
                                          if is_done0
                                          { false }
                                          else
                                          {
                                              let c2: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_array_iterator_next(
                                                      &mut pi
                                                  );
                                              let test: bool = validate_label(c2);
                                              test
                                          };
                                      if ! cont
                                      {
                                          (&mut pi)[0] = i10;
                                          (&mut pcont)[0] = false
                                      }
                                  };
                                  let test2: bool = true;
                                  test2
                              }
                              else
                              { false };
                          let _bind_c0: bool =
                              if b_success
                              {
                                  let
                                  i·:
                                  crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                  =
                                      (&pi)[0];
                                  let b_end: bool =
                                      crate::cbordetver::cbor_det_array_iterator_is_empty(i·);
                                  b_end
                              }
                              else
                              { false };
                          _bind_c0
                      }
                      else
                      { false };
                  if check_value
                  { crate::cbordetveraux::impl_map_group_result::MGOK }
                  else
                  { crate::cbordetveraux::impl_map_group_result::MGCutFail }
              },
            _ => panic!("Incomplete pattern matching")
        };
    let res2: crate::cbordetveraux::impl_map_group_result = res1;
    let test10: crate::cbordetveraux::impl_map_group_result = res2;
    let
    _bind_c0:
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty
    =
        if crate::cbordetveraux::uu___is_MGOK(test10)
        {
            let mty1: crate::cbordetver::cbor_det_int_kind =
                crate::cbordetver::cbor_det_int_kind::UInt64;
            let c11: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty1, 2u64);
            let x·1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern1: crate::cbordetver::cbor_det_view = x·1;
            let ow: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match _letpattern1
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
                      {
                          let res3: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                              crate::cbordetver::cbor_det_map_get(m3, c11);
                          res3
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            let _letpattern2: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow;
            let
            res3:
            either__CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty
            =
                match _letpattern2
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      {
                          let v1: crate::cbordetver::cbor_det_view =
                              crate::cbordetver::cbor_det_destruct(w);
                          let _letpattern10: crate::cbordetver::cbor_det_view = v1;
                          let
                          ar: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                          =
                              match _letpattern10
                              {
                                  crate::cbordetver::cbor_det_view::Array { _0: a } =>
                                    {
                                        let
                                        res3:
                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                        =
                                            crate::cbordetver::cbor_det_array_iterator_start(a);
                                        res3
                                    },
                                  _ => panic!("Incomplete pattern matching")
                              };
                          let
                          i:
                          array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env25_type_1_pretty
                          =
                              array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env25_type_1_pretty
                              {
                                  cddl_array_iterator_contents: ar,
                                  cddl_array_iterator_impl_validate: aux_env25_validate_1,
                                  cddl_array_iterator_impl_parse: aux_env25_parse_1
                              };
                          let
                          res3:
                          either__CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty
                          =
                              either__CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty::Inr
                              { v: i };
                          res3
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            let
            w11:
            either__CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty
            =
                res3;
            option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty::Some
            { v: w11 }
        }
        else
        {
            option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty::None
        };
    let
    w2:
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty
    =
        _bind_c0;
    let
    w10:
    (option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty,
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty)
    =
        (w1,w2);
    let dummy1: [u64; 1] = [0u64; 1usize];
    crate::lowstar::ignore::ignore::<&[u64]>(&dummy1);
    let mty1: crate::cbordetver::cbor_det_int_kind = crate::cbordetver::cbor_det_int_kind::UInt64;
    let c11: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty1, 3u64);
    let x·1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern1: crate::cbordetver::cbor_det_view = x·1;
    let mg1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern1
        {
            crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
              {
                  let res3: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                      crate::cbordetver::cbor_det_map_get(m3, c11);
                  res3
              },
            _ => panic!("Incomplete pattern matching")
        };
    let res3: crate::cbordetveraux::impl_map_group_result =
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
                  { crate::cbordetveraux::impl_map_group_result::MGCutFail }
              },
            _ => panic!("Incomplete pattern matching")
        };
    let res4: crate::cbordetveraux::impl_map_group_result = res3;
    let test11: crate::cbordetveraux::impl_map_group_result = res4;
    let
    _bind_c1:
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty
    =
        if crate::cbordetveraux::uu___is_MGOK(test11)
        {
            let mty2: crate::cbordetver::cbor_det_int_kind =
                crate::cbordetver::cbor_det_int_kind::UInt64;
            let c12: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty2, 3u64);
            let x·2: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern2: crate::cbordetver::cbor_det_view = x·2;
            let ow: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match _letpattern2
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
                      {
                          let res5: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                              crate::cbordetver::cbor_det_map_get(m3, c12);
                          res5
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            let _letpattern3: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow;
            let res5: either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty =
                match _letpattern3
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      {
                          let test: bool = validate_tstr(w);
                          let
                          res5:
                          either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty
                          =
                              if test
                              {
                                  let res5: &[u8] = parse_tstr(w);
                                  either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty::Inl
                                  { v: res5 }
                              }
                              else
                              {
                                  let res5: evercddl_int_pretty = parse_int(w);
                                  either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty::Inr
                                  { v: res5 }
                              };
                          res5
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            let w11: either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty =
                res5;
            option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty::Some
            { v: w11 }
        }
        else
        {
            option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty::None
        };
    let
    w20:
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty
    =
        _bind_c1;
    let
    w11:
    ((option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty,
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty),
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty)
    =
        (w10,w20);
    let dummy2: [u64; 1] = [0u64; 1usize];
    crate::lowstar::ignore::ignore::<&[u64]>(&dummy2);
    let mty2: crate::cbordetver::cbor_det_int_kind = crate::cbordetver::cbor_det_int_kind::UInt64;
    let c12: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty2, 4u64);
    let x·2: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern2: crate::cbordetver::cbor_det_view = x·2;
    let mg2: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern2
        {
            crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
              {
                  let res5: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                      crate::cbordetver::cbor_det_map_get(m3, c12);
                  res5
              },
            _ => panic!("Incomplete pattern matching")
        };
    let res5: crate::cbordetveraux::impl_map_group_result =
        match mg2
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
    let res6: crate::cbordetveraux::impl_map_group_result = res5;
    let test12: crate::cbordetveraux::impl_map_group_result = res6;
    let _bind_c2: option__COSE_Format_evercddl_bstr_pretty =
        if crate::cbordetveraux::uu___is_MGOK(test12)
        {
            let mty3: crate::cbordetver::cbor_det_int_kind =
                crate::cbordetver::cbor_det_int_kind::UInt64;
            let c13: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty3, 4u64);
            let x·3: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern3: crate::cbordetver::cbor_det_view = x·3;
            let ow: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match _letpattern3
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
                      {
                          let res7: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                              crate::cbordetver::cbor_det_map_get(m3, c13);
                          res7
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            let _letpattern4: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow;
            let res7: &[u8] =
                match _letpattern4
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      {
                          let res7: &[u8] = parse_bstr(w);
                          res7
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            let w110: &[u8] = res7;
            option__COSE_Format_evercddl_bstr_pretty::Some { v: w110 }
        }
        else
        { option__COSE_Format_evercddl_bstr_pretty::None };
    let w21: option__COSE_Format_evercddl_bstr_pretty = _bind_c2;
    let
    w12:
    (((option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty,
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty),
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty),
    option__COSE_Format_evercddl_bstr_pretty)
    =
        (w11,w21);
    let mut dummy3: [u64; 1] = [0u64; 1usize];
    let mty3: crate::cbordetver::cbor_det_int_kind = crate::cbordetver::cbor_det_int_kind::UInt64;
    let c13: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty3, 5u64);
    let x·3: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern3: crate::cbordetver::cbor_det_view = x·3;
    let mg3: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern3
        {
            crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
              {
                  let res7: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                      crate::cbordetver::cbor_det_map_get(m3, c13);
                  res7
              },
            _ => panic!("Incomplete pattern matching")
        };
    let res7: crate::cbordetveraux::impl_map_group_result =
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
    let res8: crate::cbordetveraux::impl_map_group_result = res7;
    let res10: crate::cbordetveraux::impl_map_group_result = res8;
    let test13: crate::cbordetveraux::impl_map_group_result =
        match res10
        {
            crate::cbordetveraux::impl_map_group_result::MGOK =>
              {
                  let i0: u64 = (&dummy3)[0];
                  let mty4: crate::cbordetver::cbor_det_int_kind =
                      crate::cbordetver::cbor_det_int_kind::UInt64;
                  let c14: crate::cbordetveraux::cbor_raw =
                      crate::cbordetver::cbor_det_mk_int64(mty4, 6u64);
                  let x·4: crate::cbordetver::cbor_det_view =
                      crate::cbordetver::cbor_det_destruct(c);
                  let _letpattern4: crate::cbordetver::cbor_det_view = x·4;
                  let mg4: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                      match _letpattern4
                      {
                          crate::cbordetver::cbor_det_view::Map { _0: m4 } =>
                            {
                                let res9: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                                    crate::cbordetver::cbor_det_map_get(m4, c14);
                                res9
                            },
                          _ => panic!("Incomplete pattern matching")
                      };
                  let res9: crate::cbordetveraux::impl_map_group_result =
                      match mg4
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
                  let res11: crate::cbordetveraux::impl_map_group_result = res9;
                  let res110: crate::cbordetveraux::impl_map_group_result = res11;
                  let res12: crate::cbordetveraux::impl_map_group_result =
                      match res110
                      {
                          crate::cbordetveraux::impl_map_group_result::MGOK =>
                            crate::cbordetveraux::impl_map_group_result::MGOK,
                          crate::cbordetveraux::impl_map_group_result::MGFail =>
                            {
                                (&mut dummy3)[0] = i0;
                                crate::cbordetveraux::impl_map_group_result::MGOK
                            },
                          crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                            crate::cbordetveraux::impl_map_group_result::MGCutFail,
                          _ => panic!("Precondition of the function most likely violated")
                      };
                  res12
              },
            crate::cbordetveraux::impl_map_group_result::MGFail =>
              crate::cbordetveraux::impl_map_group_result::MGFail,
            crate::cbordetveraux::impl_map_group_result::MGCutFail =>
              crate::cbordetveraux::impl_map_group_result::MGCutFail,
            _ => panic!("Precondition of the function most likely violated")
        };
    let
    _bind_c3:
    either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_FStar_Pervasives_either··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·
    =
        if crate::cbordetveraux::uu___is_MGOK(test13)
        {
            let mty4: crate::cbordetver::cbor_det_int_kind =
                crate::cbordetver::cbor_det_int_kind::UInt64;
            let c14: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty4, 5u64);
            let x·4: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern4: crate::cbordetver::cbor_det_view = x·4;
            let ow: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match _letpattern4
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
                      {
                          let res9: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                              crate::cbordetver::cbor_det_map_get(m3, c14);
                          res9
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            let _letpattern5: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow;
            let res9: &[u8] =
                match _letpattern5
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      {
                          let res9: &[u8] = parse_bstr(w);
                          res9
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            let w110: &[u8] = res9;
            let dummy10: [u64; 1] = [0u64; 1usize];
            crate::lowstar::ignore::ignore::<&[u64]>(&dummy10);
            let mty5: crate::cbordetver::cbor_det_int_kind =
                crate::cbordetver::cbor_det_int_kind::UInt64;
            let c15: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty5, 6u64);
            let x·5: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern6: crate::cbordetver::cbor_det_view = x·5;
            let mg4: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match _letpattern6
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
                      {
                          let res11: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                              crate::cbordetver::cbor_det_map_get(m3, c15);
                          res11
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            let res11: crate::cbordetveraux::impl_map_group_result =
                match mg4
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
            let res12: crate::cbordetveraux::impl_map_group_result = res11;
            let test110: crate::cbordetveraux::impl_map_group_result = res12;
            let _bind_c3: option__COSE_Format_evercddl_everparsenomatch_pretty =
                if crate::cbordetveraux::uu___is_MGOK(test110)
                {
                    let mty6: crate::cbordetver::cbor_det_int_kind =
                        crate::cbordetver::cbor_det_int_kind::UInt64;
                    let c16: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_mk_int64(mty6, 6u64);
                    let x·6: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(c);
                    let _letpattern7: crate::cbordetver::cbor_det_view = x·6;
                    let ow0: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                        match _letpattern7
                        {
                            crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
                              {
                                  let
                                  res13: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                  =
                                      crate::cbordetver::cbor_det_map_get(m3, c16);
                                  res13
                              },
                            _ => panic!("Incomplete pattern matching")
                        };
                    let _letpattern8: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow0;
                    let res13: evercddl_everparsenomatch_pretty =
                        match _letpattern8
                        {
                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                            { v: w }
                            =>
                              {
                                  let res13: evercddl_everparsenomatch_pretty =
                                      parse_everparsenomatch(w);
                                  res13
                              },
                            _ => panic!("Incomplete pattern matching")
                        };
                    let w120: evercddl_everparsenomatch_pretty = res13;
                    option__COSE_Format_evercddl_everparsenomatch_pretty::Some { v: w120 }
                }
                else
                { option__COSE_Format_evercddl_everparsenomatch_pretty::None };
            let w22: option__COSE_Format_evercddl_everparsenomatch_pretty = _bind_c3;
            let w111: (&[u8], option__COSE_Format_evercddl_everparsenomatch_pretty) = (w110,w22);
            either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_FStar_Pervasives_either··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·::Inl
            { v: w111 }
        }
        else
        {
            let mut dummy10: [u64; 1] = [0u64; 1usize];
            let mty4: crate::cbordetver::cbor_det_int_kind =
                crate::cbordetver::cbor_det_int_kind::UInt64;
            let c14: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty4, 6u64);
            let x·4: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern4: crate::cbordetver::cbor_det_view = x·4;
            let mg4: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match _letpattern4
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
                      {
                          let res9: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                              crate::cbordetver::cbor_det_map_get(m3, c14);
                          res9
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            let res9: crate::cbordetveraux::impl_map_group_result =
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
            let res11: crate::cbordetveraux::impl_map_group_result = res9;
            let res12: crate::cbordetveraux::impl_map_group_result = res11;
            let test110: crate::cbordetveraux::impl_map_group_result =
                match res12
                {
                    crate::cbordetveraux::impl_map_group_result::MGOK =>
                      {
                          let i0: u64 = (&dummy10)[0];
                          let mty5: crate::cbordetver::cbor_det_int_kind =
                              crate::cbordetver::cbor_det_int_kind::UInt64;
                          let c15: crate::cbordetveraux::cbor_raw =
                              crate::cbordetver::cbor_det_mk_int64(mty5, 5u64);
                          let x·5: crate::cbordetver::cbor_det_view =
                              crate::cbordetver::cbor_det_destruct(c);
                          let _letpattern5: crate::cbordetver::cbor_det_view = x·5;
                          let mg5: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                              match _letpattern5
                              {
                                  crate::cbordetver::cbor_det_view::Map { _0: m4 } =>
                                    {
                                        let
                                        res13:
                                        crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                        =
                                            crate::cbordetver::cbor_det_map_get(m4, c15);
                                        res13
                                    },
                                  _ => panic!("Incomplete pattern matching")
                              };
                          let res13: crate::cbordetveraux::impl_map_group_result =
                              match mg5
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
                          let res14: crate::cbordetveraux::impl_map_group_result = res13;
                          let res110: crate::cbordetveraux::impl_map_group_result = res14;
                          let res15: crate::cbordetveraux::impl_map_group_result =
                              match res110
                              {
                                  crate::cbordetveraux::impl_map_group_result::MGOK =>
                                    crate::cbordetveraux::impl_map_group_result::MGOK,
                                  crate::cbordetveraux::impl_map_group_result::MGFail =>
                                    {
                                        (&mut dummy10)[0] = i0;
                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                    },
                                  crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                                    crate::cbordetveraux::impl_map_group_result::MGCutFail,
                                  _ => panic!("Precondition of the function most likely violated")
                              };
                          res15
                      },
                    crate::cbordetveraux::impl_map_group_result::MGFail =>
                      crate::cbordetveraux::impl_map_group_result::MGFail,
                    crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                      crate::cbordetveraux::impl_map_group_result::MGCutFail,
                    _ => panic!("Precondition of the function most likely violated")
                };
            let
            _bind_c3:
            either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_·FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·
            =
                if crate::cbordetveraux::uu___is_MGOK(test110)
                {
                    let mty5: crate::cbordetver::cbor_det_int_kind =
                        crate::cbordetver::cbor_det_int_kind::UInt64;
                    let c15: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_mk_int64(mty5, 6u64);
                    let x·5: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(c);
                    let _letpattern5: crate::cbordetver::cbor_det_view = x·5;
                    let ow: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                        match _letpattern5
                        {
                            crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
                              {
                                  let
                                  res13: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                  =
                                      crate::cbordetver::cbor_det_map_get(m3, c15);
                                  res13
                              },
                            _ => panic!("Incomplete pattern matching")
                        };
                    let _letpattern6: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow;
                    let res13: &[u8] =
                        match _letpattern6
                        {
                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                            { v: w }
                            =>
                              {
                                  let res13: &[u8] = parse_bstr(w);
                                  res13
                              },
                            _ => panic!("Incomplete pattern matching")
                        };
                    let w110: &[u8] = res13;
                    let dummy20: [u64; 1] = [0u64; 1usize];
                    crate::lowstar::ignore::ignore::<&[u64]>(&dummy20);
                    let mty6: crate::cbordetver::cbor_det_int_kind =
                        crate::cbordetver::cbor_det_int_kind::UInt64;
                    let c16: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_mk_int64(mty6, 5u64);
                    let x·6: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(c);
                    let _letpattern7: crate::cbordetver::cbor_det_view = x·6;
                    let mg5: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                        match _letpattern7
                        {
                            crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
                              {
                                  let
                                  res14: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                  =
                                      crate::cbordetver::cbor_det_map_get(m3, c16);
                                  res14
                              },
                            _ => panic!("Incomplete pattern matching")
                        };
                    let res14: crate::cbordetveraux::impl_map_group_result =
                        match mg5
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
                    let res15: crate::cbordetveraux::impl_map_group_result = res14;
                    let test120: crate::cbordetveraux::impl_map_group_result = res15;
                    let _bind_c3: option__COSE_Format_evercddl_everparsenomatch_pretty =
                        if crate::cbordetveraux::uu___is_MGOK(test120)
                        {
                            let mty7: crate::cbordetver::cbor_det_int_kind =
                                crate::cbordetver::cbor_det_int_kind::UInt64;
                            let c17: crate::cbordetveraux::cbor_raw =
                                crate::cbordetver::cbor_det_mk_int64(mty7, 5u64);
                            let x·7: crate::cbordetver::cbor_det_view =
                                crate::cbordetver::cbor_det_destruct(c);
                            let _letpattern8: crate::cbordetver::cbor_det_view = x·7;
                            let ow0: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                                match _letpattern8
                                {
                                    crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
                                      {
                                          let
                                          res16:
                                          crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                          =
                                              crate::cbordetver::cbor_det_map_get(m3, c17);
                                          res16
                                      },
                                    _ => panic!("Incomplete pattern matching")
                                };
                            let
                            _letpattern9: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                            =
                                ow0;
                            let res16: evercddl_everparsenomatch_pretty =
                                match _letpattern9
                                {
                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                    { v: w }
                                    =>
                                      {
                                          let res16: evercddl_everparsenomatch_pretty =
                                              parse_everparsenomatch(w);
                                          res16
                                      },
                                    _ => panic!("Incomplete pattern matching")
                                };
                            let w120: evercddl_everparsenomatch_pretty = res16;
                            option__COSE_Format_evercddl_everparsenomatch_pretty::Some { v: w120 }
                        }
                        else
                        { option__COSE_Format_evercddl_everparsenomatch_pretty::None };
                    let w22: option__COSE_Format_evercddl_everparsenomatch_pretty = _bind_c3;
                    let w111: (&[u8], option__COSE_Format_evercddl_everparsenomatch_pretty) =
                        (w110,w22);
                    either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_·FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·::Inl
                    { v: w111 }
                }
                else
                {
                    let dummy20: [u64; 1] = [0u64; 1usize];
                    crate::lowstar::ignore::ignore::<&[u64]>(&dummy20);
                    let mty5: crate::cbordetver::cbor_det_int_kind =
                        crate::cbordetver::cbor_det_int_kind::UInt64;
                    let c15: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_mk_int64(mty5, 6u64);
                    let x·5: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(c);
                    let _letpattern5: crate::cbordetver::cbor_det_view = x·5;
                    let mg5: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                        match _letpattern5
                        {
                            crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
                              {
                                  let
                                  res13: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                  =
                                      crate::cbordetver::cbor_det_map_get(m3, c15);
                                  res13
                              },
                            _ => panic!("Incomplete pattern matching")
                        };
                    let res13: crate::cbordetveraux::impl_map_group_result =
                        match mg5
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
                    let res14: crate::cbordetveraux::impl_map_group_result = res13;
                    let test120: crate::cbordetveraux::impl_map_group_result = res14;
                    let _bind_c3: option__COSE_Format_evercddl_everparsenomatch_pretty =
                        if crate::cbordetveraux::uu___is_MGOK(test120)
                        {
                            let mty6: crate::cbordetver::cbor_det_int_kind =
                                crate::cbordetver::cbor_det_int_kind::UInt64;
                            let c16: crate::cbordetveraux::cbor_raw =
                                crate::cbordetver::cbor_det_mk_int64(mty6, 6u64);
                            let x·6: crate::cbordetver::cbor_det_view =
                                crate::cbordetver::cbor_det_destruct(c);
                            let _letpattern6: crate::cbordetver::cbor_det_view = x·6;
                            let ow: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                                match _letpattern6
                                {
                                    crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
                                      {
                                          let
                                          res15:
                                          crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                          =
                                              crate::cbordetver::cbor_det_map_get(m3, c16);
                                          res15
                                      },
                                    _ => panic!("Incomplete pattern matching")
                                };
                            let
                            _letpattern7: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                            =
                                ow;
                            let res15: evercddl_everparsenomatch_pretty =
                                match _letpattern7
                                {
                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                    { v: w }
                                    =>
                                      {
                                          let res15: evercddl_everparsenomatch_pretty =
                                              parse_everparsenomatch(w);
                                          res15
                                      },
                                    _ => panic!("Incomplete pattern matching")
                                };
                            let w110: evercddl_everparsenomatch_pretty = res15;
                            option__COSE_Format_evercddl_everparsenomatch_pretty::Some { v: w110 }
                        }
                        else
                        { option__COSE_Format_evercddl_everparsenomatch_pretty::None };
                    let w110: option__COSE_Format_evercddl_everparsenomatch_pretty = _bind_c3;
                    let dummy21: [u64; 1] = [0u64; 1usize];
                    crate::lowstar::ignore::ignore::<&[u64]>(&dummy21);
                    let mty6: crate::cbordetver::cbor_det_int_kind =
                        crate::cbordetver::cbor_det_int_kind::UInt64;
                    let c16: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_mk_int64(mty6, 5u64);
                    let x·6: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(c);
                    let _letpattern6: crate::cbordetver::cbor_det_view = x·6;
                    let mg6: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                        match _letpattern6
                        {
                            crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
                              {
                                  let
                                  res15: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                  =
                                      crate::cbordetver::cbor_det_map_get(m3, c16);
                                  res15
                              },
                            _ => panic!("Incomplete pattern matching")
                        };
                    let res15: crate::cbordetveraux::impl_map_group_result =
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
                    let res16: crate::cbordetveraux::impl_map_group_result = res15;
                    let test121: crate::cbordetveraux::impl_map_group_result = res16;
                    let _bind_c4: option__COSE_Format_evercddl_everparsenomatch_pretty =
                        if crate::cbordetveraux::uu___is_MGOK(test121)
                        {
                            let mty7: crate::cbordetver::cbor_det_int_kind =
                                crate::cbordetver::cbor_det_int_kind::UInt64;
                            let c17: crate::cbordetveraux::cbor_raw =
                                crate::cbordetver::cbor_det_mk_int64(mty7, 5u64);
                            let x·7: crate::cbordetver::cbor_det_view =
                                crate::cbordetver::cbor_det_destruct(c);
                            let _letpattern7: crate::cbordetver::cbor_det_view = x·7;
                            let ow: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                                match _letpattern7
                                {
                                    crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
                                      {
                                          let
                                          res17:
                                          crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                          =
                                              crate::cbordetver::cbor_det_map_get(m3, c17);
                                          res17
                                      },
                                    _ => panic!("Incomplete pattern matching")
                                };
                            let
                            _letpattern8: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                            =
                                ow;
                            let res17: evercddl_everparsenomatch_pretty =
                                match _letpattern8
                                {
                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                    { v: w }
                                    =>
                                      {
                                          let res17: evercddl_everparsenomatch_pretty =
                                              parse_everparsenomatch(w);
                                          res17
                                      },
                                    _ => panic!("Incomplete pattern matching")
                                };
                            let w120: evercddl_everparsenomatch_pretty = res17;
                            option__COSE_Format_evercddl_everparsenomatch_pretty::Some { v: w120 }
                        }
                        else
                        { option__COSE_Format_evercddl_everparsenomatch_pretty::None };
                    let w22: option__COSE_Format_evercddl_everparsenomatch_pretty = _bind_c4;
                    let
                    w23:
                    (option__COSE_Format_evercddl_everparsenomatch_pretty,
                    option__COSE_Format_evercddl_everparsenomatch_pretty)
                    =
                        (w110,w22);
                    either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_·FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·::Inr
                    { v: w23 }
                };
            let
            w22:
            either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_·FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·
            =
                _bind_c3;
            either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_FStar_Pervasives_either··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·::Inr
            { v: w22 }
        };
    let
    w22:
    either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_FStar_Pervasives_either··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·
    =
        _bind_c3;
    let
    w13:
    ((((option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty,
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty),
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty),
    option__COSE_Format_evercddl_bstr_pretty),
    either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_FStar_Pervasives_either··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·)
    =
        (w12,w22);
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern4: crate::cbordetver::cbor_det_view = v1;
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
        match _letpattern4
        {
            crate::cbordetver::cbor_det_view::Map { _0: a } =>
              {
                  let
                  res9: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                  =
                      crate::cbordetver::cbor_det_map_iterator_start(a);
                  res9
              },
            _ => panic!("Incomplete pattern matching")
        };
    let
    rres:
    map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
    =
        map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
        {
            cddl_map_iterator_contents: i,
            cddl_map_iterator_impl_validate1: aux_env25_validate_2,
            cddl_map_iterator_impl_parse1: aux_env25_parse_2,
            cddl_map_iterator_impl_validate_ex: aux_env25_validate_3,
            cddl_map_iterator_impl_validate2: aux_env25_validate_4,
            cddl_map_iterator_impl_parse2: aux_env25_parse_4
        };
    let
    w23:
    either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty
    =
        either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty::Inr
        { v: rres };
    let
    res11:
    (((((option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty,
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty),
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty),
    option__COSE_Format_evercddl_bstr_pretty),
    either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_FStar_Pervasives_either··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·),
    either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty)
    =
        (w13,w23);
    let res20: evercddl_header_map_pretty = evercddl_header_map_pretty_right(res11);
    res20
}

/**
Serializer for evercddl_header_map
*/
pub fn
serialize_header_map(c: evercddl_header_map_pretty, out: &mut [u8]) ->
    usize
{
    let
    c·:
    (((((option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty,
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty),
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty),
    option__COSE_Format_evercddl_bstr_pretty),
    either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_FStar_Pervasives_either··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·),
    either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty)
    =
        evercddl_header_map_pretty_left(c);
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let
    _letpattern:
    (((((option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty,
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty),
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty),
    option__COSE_Format_evercddl_bstr_pretty),
    either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_FStar_Pervasives_either··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·),
    either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty)
    =
        c·;
    let res: bool =
        {
            let
            c1:
            ((((option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty,
            option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty),
            option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty),
            option__COSE_Format_evercddl_bstr_pretty),
            either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_FStar_Pervasives_either··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·)
            =
                _letpattern.0;
            let
            c2:
            either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty
            =
                _letpattern.1;
            let
            _letpattern1:
            ((((option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty,
            option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty),
            option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty),
            option__COSE_Format_evercddl_bstr_pretty),
            either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_FStar_Pervasives_either··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·)
            =
                c1;
            let res1: bool =
                {
                    let
                    c11:
                    (((option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty,
                    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty),
                    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty),
                    option__COSE_Format_evercddl_bstr_pretty)
                    =
                        _letpattern1.0;
                    let
                    c21:
                    either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_FStar_Pervasives_either··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·
                    =
                        _letpattern1.1;
                    let
                    _letpattern2:
                    (((option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty,
                    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty),
                    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty),
                    option__COSE_Format_evercddl_bstr_pretty)
                    =
                        c11;
                    let res1: bool =
                        {
                            let
                            c12:
                            ((option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty,
                            option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty),
                            option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty)
                            =
                                _letpattern2.0;
                            let c22: option__COSE_Format_evercddl_bstr_pretty = _letpattern2.1;
                            let
                            _letpattern3:
                            ((option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty,
                            option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty),
                            option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty)
                            =
                                c12;
                            let res1: bool =
                                {
                                    let
                                    c13:
                                    (option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty,
                                    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty)
                                    =
                                        _letpattern3.0;
                                    let
                                    c23:
                                    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty
                                    =
                                        _letpattern3.1;
                                    let
                                    _letpattern4:
                                    (option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty,
                                    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty)
                                    =
                                        c13;
                                    let res1: bool =
                                        {
                                            let
                                            c14:
                                            option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty
                                            =
                                                _letpattern4.0;
                                            let
                                            c24:
                                            option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty
                                            =
                                                _letpattern4.1;
                                            let res1: bool =
                                                match c14
                                                {
                                                    option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty::Some
                                                    { v: c15 }
                                                    =>
                                                      {
                                                          let count: u64 = (&pcount)[0];
                                                          let res: bool =
                                                              if count < 18446744073709551615u64
                                                              {
                                                                  let size0: usize = (&psize)[0];
                                                                  let
                                                                  _letpattern5:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size0);
                                                                  let _out0: &[u8] = _letpattern5.0;
                                                                  let out1: &mut [u8] =
                                                                      _letpattern5.1;
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
                                                                  res:
                                                                  crate::cbordetver::option__size_t
                                                                  =
                                                                      crate::cbordetver::cbor_det_serialize(
                                                                          c3,
                                                                          out1
                                                                      );
                                                                  let res0: usize =
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
                                                                  let res1: usize = res0;
                                                                  if res1 > 0usize
                                                                  {
                                                                      let size1: usize =
                                                                          size0.wrapping_add(res1);
                                                                      let
                                                                      _letpattern6:
                                                                      (&mut [u8], &mut [u8])
                                                                      =
                                                                          out.split_at_mut(size1);
                                                                      let _out01: &[u8] =
                                                                          _letpattern6.0;
                                                                      let out2: &mut [u8] =
                                                                          _letpattern6.1;
                                                                      let res2: usize =
                                                                          match c15
                                                                          {
                                                                              evercddl_label::Inl
                                                                              { v: c16 }
                                                                              =>
                                                                                {
                                                                                    let
                                                                                    res2: usize
                                                                                    =
                                                                                        serialize_int(
                                                                                            c16,
                                                                                            out2
                                                                                        );
                                                                                    res2
                                                                                },
                                                                              evercddl_label::Inr
                                                                              { v: c25 }
                                                                              =>
                                                                                {
                                                                                    let
                                                                                    res2: usize
                                                                                    =
                                                                                        serialize_tstr(
                                                                                            c25,
                                                                                            out2
                                                                                        );
                                                                                    res2
                                                                                },
                                                                              _ =>
                                                                                panic!(
                                                                                    "Incomplete pattern matching"
                                                                                )
                                                                          };
                                                                      if res2 > 0usize
                                                                      {
                                                                          let size2: usize =
                                                                              size1.wrapping_add(
                                                                                  res2
                                                                              );
                                                                          let
                                                                          _letpattern7:
                                                                          (&mut [u8], &mut [u8])
                                                                          =
                                                                              out.split_at_mut(
                                                                                  size2
                                                                              );
                                                                          let out012: &mut [u8] =
                                                                              _letpattern7.0;
                                                                          let res3: bool =
                                                                              crate::cbordetver::cbor_det_serialize_map_insert(
                                                                                  out012,
                                                                                  size0,
                                                                                  size1
                                                                              );
                                                                          if res3
                                                                          {
                                                                              (&mut psize)[0] =
                                                                                  size2;
                                                                              (&mut pcount)[0] =
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
                                                              { false };
                                                          res
                                                      },
                                                    option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty::None
                                                    => true,
                                                    _ => panic!("Incomplete pattern matching")
                                                };
                                            if res1
                                            {
                                                let res2: bool =
                                                    match c24
                                                    {
                                                        option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty::Some
                                                        { v: c15 }
                                                        =>
                                                          {
                                                              let count: u64 = (&pcount)[0];
                                                              let res: bool =
                                                                  if count < 18446744073709551615u64
                                                                  {
                                                                      let size0: usize =
                                                                          (&psize)[0];
                                                                      let
                                                                      _letpattern5:
                                                                      (&mut [u8], &mut [u8])
                                                                      =
                                                                          out.split_at_mut(size0);
                                                                      let _out0: &[u8] =
                                                                          _letpattern5.0;
                                                                      let out1: &mut [u8] =
                                                                          _letpattern5.1;
                                                                      let
                                                                      mty:
                                                                      crate::cbordetver::cbor_det_int_kind
                                                                      =
                                                                          crate::cbordetver::cbor_det_int_kind::UInt64;
                                                                      let
                                                                      c3:
                                                                      crate::cbordetveraux::cbor_raw
                                                                      =
                                                                          crate::cbordetver::cbor_det_mk_int64(
                                                                              mty,
                                                                              2u64
                                                                          );
                                                                      let
                                                                      res:
                                                                      crate::cbordetver::option__size_t
                                                                      =
                                                                          crate::cbordetver::cbor_det_serialize(
                                                                              c3,
                                                                              out1
                                                                          );
                                                                      let res0: usize =
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
                                                                      let res11: usize = res0;
                                                                      if res11 > 0usize
                                                                      {
                                                                          let size1: usize =
                                                                              size0.wrapping_add(
                                                                                  res11
                                                                              );
                                                                          let
                                                                          _letpattern6:
                                                                          (&mut [u8], &mut [u8])
                                                                          =
                                                                              out.split_at_mut(
                                                                                  size1
                                                                              );
                                                                          let _out01: &[u8] =
                                                                              _letpattern6.0;
                                                                          let out2: &mut [u8] =
                                                                              _letpattern6.1;
                                                                          let
                                                                          mut pcount1: [u64; 1]
                                                                          =
                                                                              [0u64; 1usize];
                                                                          let
                                                                          mut psize1: [usize; 1]
                                                                          =
                                                                              [0usize; 1usize];
                                                                          let res2: bool =
                                                                              match c15
                                                                              {
                                                                                  either__CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty::Inl
                                                                                  { v: c16 }
                                                                                  =>
                                                                                    {
                                                                                        let
                                                                                        res2: bool
                                                                                        =
                                                                                            if
                                                                                            c16.len(

                                                                                            )
                                                                                            ==
                                                                                            0usize
                                                                                            {
                                                                                                false
                                                                                            }
                                                                                            else
                                                                                            {
                                                                                                let
                                                                                                mut
                                                                                                pres:
                                                                                                [bool;
                                                                                                1]
                                                                                                =
                                                                                                    [true;
                                                                                                        1usize];
                                                                                                let
                                                                                                mut
                                                                                                pi:
                                                                                                [usize;
                                                                                                1]
                                                                                                =
                                                                                                    [0usize;
                                                                                                        1usize];
                                                                                                let
                                                                                                slen:
                                                                                                usize
                                                                                                =
                                                                                                    c16.len(

                                                                                                    );
                                                                                                let
                                                                                                res2:
                                                                                                bool
                                                                                                =
                                                                                                    (&pres)[0];
                                                                                                let
                                                                                                mut
                                                                                                cond:
                                                                                                bool
                                                                                                =
                                                                                                    if
                                                                                                    res2
                                                                                                    {
                                                                                                        let
                                                                                                        i:
                                                                                                        usize
                                                                                                        =
                                                                                                            (&pi)[0];
                                                                                                        i
                                                                                                        <
                                                                                                        slen
                                                                                                    }
                                                                                                    else
                                                                                                    {
                                                                                                        false
                                                                                                    };
                                                                                                while
                                                                                                cond
                                                                                                {
                                                                                                    let
                                                                                                    i:
                                                                                                    usize
                                                                                                    =
                                                                                                        (&pi)[0];
                                                                                                    let
                                                                                                    x:
                                                                                                    evercddl_label_pretty
                                                                                                    =
                                                                                                        c16[i];
                                                                                                    let
                                                                                                    res3:
                                                                                                    bool
                                                                                                    =
                                                                                                        aux_env25_serialize_1(
                                                                                                            x,
                                                                                                            out2,
                                                                                                            &mut
                                                                                                            pcount1,
                                                                                                            &mut
                                                                                                            psize1
                                                                                                        );
                                                                                                    if
                                                                                                    res3
                                                                                                    {
                                                                                                        let
                                                                                                        i·:
                                                                                                        usize
                                                                                                        =
                                                                                                            i.wrapping_add(
                                                                                                                1usize
                                                                                                            );
                                                                                                        (&mut
                                                                                                        pi)[0] =
                                                                                                            i·
                                                                                                    }
                                                                                                    else
                                                                                                    {
                                                                                                        (&mut
                                                                                                        pres)[0] =
                                                                                                            false
                                                                                                    };
                                                                                                    let
                                                                                                    res4:
                                                                                                    bool
                                                                                                    =
                                                                                                        (&pres)[0];
                                                                                                    let
                                                                                                    ite:
                                                                                                    bool
                                                                                                    =
                                                                                                        if
                                                                                                        res4
                                                                                                        {
                                                                                                            let
                                                                                                            i0:
                                                                                                            usize
                                                                                                            =
                                                                                                                (&pi)[0];
                                                                                                            i0
                                                                                                            <
                                                                                                            slen
                                                                                                        }
                                                                                                        else
                                                                                                        {
                                                                                                            false
                                                                                                        };
                                                                                                    cond =
                                                                                                        ite
                                                                                                };
                                                                                                (&pres)[0]
                                                                                            };
                                                                                        res2
                                                                                    },
                                                                                  either__CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty::Inr
                                                                                  { v: c25 }
                                                                                  =>
                                                                                    {
                                                                                        let
                                                                                        res2: bool
                                                                                        =
                                                                                            crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                                                                c25.cddl_array_iterator_contents
                                                                                            );
                                                                                        let
                                                                                        em: bool
                                                                                        =
                                                                                            res2;
                                                                                        let
                                                                                        res3: bool
                                                                                        =
                                                                                            if em
                                                                                            {
                                                                                                false
                                                                                            }
                                                                                            else
                                                                                            {
                                                                                                let
                                                                                                mut
                                                                                                pc:
                                                                                                [array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env25_type_1_pretty;
                                                                                                1]
                                                                                                =
                                                                                                    [c25;
                                                                                                        1usize];
                                                                                                let
                                                                                                mut
                                                                                                pres:
                                                                                                [bool;
                                                                                                1]
                                                                                                =
                                                                                                    [true;
                                                                                                        1usize];
                                                                                                let
                                                                                                res3:
                                                                                                bool
                                                                                                =
                                                                                                    (&pres)[0];
                                                                                                let
                                                                                                mut
                                                                                                cond:
                                                                                                bool
                                                                                                =
                                                                                                    if
                                                                                                    res3
                                                                                                    {
                                                                                                        let
                                                                                                        c30:
                                                                                                        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env25_type_1_pretty
                                                                                                        =
                                                                                                            (&pc)[0];
                                                                                                        let
                                                                                                        res20:
                                                                                                        bool
                                                                                                        =
                                                                                                            crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                                                                                c30.cddl_array_iterator_contents
                                                                                                            );
                                                                                                        let
                                                                                                        em1:
                                                                                                        bool
                                                                                                        =
                                                                                                            res20;
                                                                                                        !
                                                                                                        em1
                                                                                                    }
                                                                                                    else
                                                                                                    {
                                                                                                        false
                                                                                                    };
                                                                                                while
                                                                                                cond
                                                                                                {
                                                                                                    let
                                                                                                    i:
                                                                                                    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env25_type_1_pretty
                                                                                                    =
                                                                                                        (&pc)[0];
                                                                                                    let
                                                                                                    len0:
                                                                                                    u64
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
                                                                                                    _test:
                                                                                                    bool
                                                                                                    =
                                                                                                        (i.cddl_array_iterator_impl_validate)(
                                                                                                            &mut
                                                                                                            pj
                                                                                                        );
                                                                                                    crate::lowstar::ignore::ignore::<bool>(
                                                                                                        _test
                                                                                                    );
                                                                                                    let
                                                                                                    ji:
                                                                                                    crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                                                                    =
                                                                                                        (&pj)[0];
                                                                                                    let
                                                                                                    len1:
                                                                                                    u64
                                                                                                    =
                                                                                                        crate::cbordetver::cbor_det_array_iterator_length(
                                                                                                            ji
                                                                                                        );
                                                                                                    let
                                                                                                    j:
                                                                                                    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env25_type_1_pretty
                                                                                                    =
                                                                                                        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env25_type_1_pretty
                                                                                                        {
                                                                                                            cddl_array_iterator_contents:
                                                                                                            ji,
                                                                                                            cddl_array_iterator_impl_validate:
                                                                                                            i.cddl_array_iterator_impl_validate,
                                                                                                            cddl_array_iterator_impl_parse:
                                                                                                            i.cddl_array_iterator_impl_parse
                                                                                                        };
                                                                                                    (&mut
                                                                                                    pc)[0] =
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
                                                                                                    res4:
                                                                                                    evercddl_label_pretty
                                                                                                    =
                                                                                                        (i.cddl_array_iterator_impl_parse)(
                                                                                                            tri
                                                                                                        );
                                                                                                    let
                                                                                                    x:
                                                                                                    evercddl_label_pretty
                                                                                                    =
                                                                                                        res4;
                                                                                                    let
                                                                                                    res5:
                                                                                                    bool
                                                                                                    =
                                                                                                        aux_env25_serialize_1(
                                                                                                            x,
                                                                                                            out2,
                                                                                                            &mut
                                                                                                            pcount1,
                                                                                                            &mut
                                                                                                            psize1
                                                                                                        );
                                                                                                    if
                                                                                                    !
                                                                                                    res5
                                                                                                    {
                                                                                                        (&mut
                                                                                                        pres)[0] =
                                                                                                            false
                                                                                                    };
                                                                                                    let
                                                                                                    res6:
                                                                                                    bool
                                                                                                    =
                                                                                                        (&pres)[0];
                                                                                                    let
                                                                                                    ite:
                                                                                                    bool
                                                                                                    =
                                                                                                        if
                                                                                                        res6
                                                                                                        {
                                                                                                            let
                                                                                                            c30:
                                                                                                            array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env25_type_1_pretty
                                                                                                            =
                                                                                                                (&pc)[0];
                                                                                                            let
                                                                                                            res20:
                                                                                                            bool
                                                                                                            =
                                                                                                                crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                                                                                    c30.cddl_array_iterator_contents
                                                                                                                );
                                                                                                            let
                                                                                                            em1:
                                                                                                            bool
                                                                                                            =
                                                                                                                res20;
                                                                                                            !
                                                                                                            em1
                                                                                                        }
                                                                                                        else
                                                                                                        {
                                                                                                            false
                                                                                                        };
                                                                                                    cond =
                                                                                                        ite
                                                                                                };
                                                                                                (&pres)[0]
                                                                                            };
                                                                                        res3
                                                                                    },
                                                                                  _ =>
                                                                                    panic!(
                                                                                        "Incomplete pattern matching"
                                                                                    )
                                                                              };
                                                                          let _bind_c: usize =
                                                                              if res2
                                                                              {
                                                                                  let size: usize =
                                                                                      (&psize1)[0];
                                                                                  let count1: u64 =
                                                                                      (&pcount1)[0];
                                                                                  crate::cbordetver::cbor_det_serialize_array(
                                                                                      count1,
                                                                                      out2,
                                                                                      size
                                                                                  )
                                                                              }
                                                                              else
                                                                              { 0usize };
                                                                          let res20: usize =
                                                                              _bind_c;
                                                                          if res20 > 0usize
                                                                          {
                                                                              let size2: usize =
                                                                                  size1.wrapping_add(
                                                                                      res20
                                                                                  );
                                                                              let
                                                                              _letpattern7:
                                                                              (&mut [u8], &mut [u8])
                                                                              =
                                                                                  out.split_at_mut(
                                                                                      size2
                                                                                  );
                                                                              let
                                                                              out012: &mut [u8]
                                                                              =
                                                                                  _letpattern7.0;
                                                                              let res3: bool =
                                                                                  crate::cbordetver::cbor_det_serialize_map_insert(
                                                                                      out012,
                                                                                      size0,
                                                                                      size1
                                                                                  );
                                                                              if res3
                                                                              {
                                                                                  (&mut psize)[0] =
                                                                                      size2;
                                                                                  (&mut pcount)[0] =
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
                                                                  { false };
                                                              res
                                                          },
                                                        option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env25_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env25_type_1_pretty::None
                                                        => true,
                                                        _ => panic!("Incomplete pattern matching")
                                                    };
                                                res2
                                            }
                                            else
                                            { false }
                                        };
                                    if res1
                                    {
                                        let res2: bool =
                                            match c23
                                            {
                                                option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty::Some
                                                { v: c14 }
                                                =>
                                                  {
                                                      let count: u64 = (&pcount)[0];
                                                      let res: bool =
                                                          if count < 18446744073709551615u64
                                                          {
                                                              let size0: usize = (&psize)[0];
                                                              let
                                                              _letpattern40: (&mut [u8], &mut [u8])
                                                              =
                                                                  out.split_at_mut(size0);
                                                              let _out0: &[u8] = _letpattern40.0;
                                                              let out1: &mut [u8] = _letpattern40.1;
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
                                                                      3u64
                                                                  );
                                                              let
                                                              res: crate::cbordetver::option__size_t
                                                              =
                                                                  crate::cbordetver::cbor_det_serialize(
                                                                      c3,
                                                                      out1
                                                                  );
                                                              let res0: usize =
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
                                                              let res11: usize = res0;
                                                              if res11 > 0usize
                                                              {
                                                                  let size1: usize =
                                                                      size0.wrapping_add(res11);
                                                                  let
                                                                  _letpattern5:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size1);
                                                                  let _out01: &[u8] =
                                                                      _letpattern5.0;
                                                                  let out2: &mut [u8] =
                                                                      _letpattern5.1;
                                                                  let res2: usize =
                                                                      match c14
                                                                      {
                                                                          either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty::Inl
                                                                          { v: c15 }
                                                                          =>
                                                                            {
                                                                                let res2: usize =
                                                                                    serialize_tstr(
                                                                                        c15,
                                                                                        out2
                                                                                    );
                                                                                res2
                                                                            },
                                                                          either__COSE_Format_evercddl_tstr_pretty_COSE_Format_evercddl_int_pretty::Inr
                                                                          { v: c24 }
                                                                          =>
                                                                            {
                                                                                let res2: usize =
                                                                                    serialize_int(
                                                                                        c24,
                                                                                        out2
                                                                                    );
                                                                                res2
                                                                            },
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
                                                                      _letpattern6:
                                                                      (&mut [u8], &mut [u8])
                                                                      =
                                                                          out.split_at_mut(size2);
                                                                      let out012: &mut [u8] =
                                                                          _letpattern6.0;
                                                                      let res3: bool =
                                                                          crate::cbordetver::cbor_det_serialize_map_insert(
                                                                              out012,
                                                                              size0,
                                                                              size1
                                                                          );
                                                                      if res3
                                                                      {
                                                                          (&mut psize)[0] = size2;
                                                                          (&mut pcount)[0] =
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
                                                          { false };
                                                      res
                                                  },
                                                option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty::None
                                                => true,
                                                _ => panic!("Incomplete pattern matching")
                                            };
                                        res2
                                    }
                                    else
                                    { false }
                                };
                            if res1
                            {
                                let res2: bool =
                                    match c22
                                    {
                                        option__COSE_Format_evercddl_bstr_pretty::Some { v: c13 } =>
                                          {
                                              let count: u64 = (&pcount)[0];
                                              let res: bool =
                                                  if count < 18446744073709551615u64
                                                  {
                                                      let size0: usize = (&psize)[0];
                                                      let _letpattern30: (&mut [u8], &mut [u8]) =
                                                          out.split_at_mut(size0);
                                                      let _out0: &[u8] = _letpattern30.0;
                                                      let out1: &mut [u8] = _letpattern30.1;
                                                      let
                                                      mty: crate::cbordetver::cbor_det_int_kind
                                                      =
                                                          crate::cbordetver::cbor_det_int_kind::UInt64;
                                                      let c3: crate::cbordetveraux::cbor_raw =
                                                          crate::cbordetver::cbor_det_mk_int64(
                                                              mty,
                                                              4u64
                                                          );
                                                      let res: crate::cbordetver::option__size_t =
                                                          crate::cbordetver::cbor_det_serialize(
                                                              c3,
                                                              out1
                                                          );
                                                      let res0: usize =
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
                                                      let res11: usize = res0;
                                                      if res11 > 0usize
                                                      {
                                                          let size1: usize =
                                                              size0.wrapping_add(res11);
                                                          let _letpattern4: (&mut [u8], &mut [u8]) =
                                                              out.split_at_mut(size1);
                                                          let _out01: &[u8] = _letpattern4.0;
                                                          let out2: &mut [u8] = _letpattern4.1;
                                                          let res2: usize =
                                                              serialize_bstr(c13, out2);
                                                          if res2 > 0usize
                                                          {
                                                              let size2: usize =
                                                                  size1.wrapping_add(res2);
                                                              let
                                                              _letpattern5: (&mut [u8], &mut [u8])
                                                              =
                                                                  out.split_at_mut(size2);
                                                              let out012: &mut [u8] =
                                                                  _letpattern5.0;
                                                              let res3: bool =
                                                                  crate::cbordetver::cbor_det_serialize_map_insert(
                                                                      out012,
                                                                      size0,
                                                                      size1
                                                                  );
                                                              if res3
                                                              {
                                                                  (&mut psize)[0] = size2;
                                                                  (&mut pcount)[0] =
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
                                              res
                                          },
                                        option__COSE_Format_evercddl_bstr_pretty::None => true,
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                res2
                            }
                            else
                            { false }
                        };
                    if res1
                    {
                        let res2: bool =
                            match c21
                            {
                                either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_FStar_Pervasives_either··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·::Inl
                                { v: c12 }
                                =>
                                  {
                                      let
                                      _letpattern20:
                                      (&[u8], option__COSE_Format_evercddl_everparsenomatch_pretty)
                                      =
                                          c12;
                                      let res: bool =
                                          {
                                              let c13: &[u8] = _letpattern20.0;
                                              let
                                              c22:
                                              option__COSE_Format_evercddl_everparsenomatch_pretty
                                              =
                                                  _letpattern20.1;
                                              let count: u64 = (&pcount)[0];
                                              let res11: bool =
                                                  if count < 18446744073709551615u64
                                                  {
                                                      let size0: usize = (&psize)[0];
                                                      let _letpattern3: (&mut [u8], &mut [u8]) =
                                                          out.split_at_mut(size0);
                                                      let _out0: &[u8] = _letpattern3.0;
                                                      let out1: &mut [u8] = _letpattern3.1;
                                                      let
                                                      mty: crate::cbordetver::cbor_det_int_kind
                                                      =
                                                          crate::cbordetver::cbor_det_int_kind::UInt64;
                                                      let c3: crate::cbordetveraux::cbor_raw =
                                                          crate::cbordetver::cbor_det_mk_int64(
                                                              mty,
                                                              5u64
                                                          );
                                                      let res: crate::cbordetver::option__size_t =
                                                          crate::cbordetver::cbor_det_serialize(
                                                              c3,
                                                              out1
                                                          );
                                                      let res0: usize =
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
                                                      let res11: usize = res0;
                                                      if res11 > 0usize
                                                      {
                                                          let size1: usize =
                                                              size0.wrapping_add(res11);
                                                          let _letpattern4: (&mut [u8], &mut [u8]) =
                                                              out.split_at_mut(size1);
                                                          let _out01: &[u8] = _letpattern4.0;
                                                          let out2: &mut [u8] = _letpattern4.1;
                                                          let res2: usize =
                                                              serialize_bstr(c13, out2);
                                                          if res2 > 0usize
                                                          {
                                                              let size2: usize =
                                                                  size1.wrapping_add(res2);
                                                              let
                                                              _letpattern5: (&mut [u8], &mut [u8])
                                                              =
                                                                  out.split_at_mut(size2);
                                                              let out012: &mut [u8] =
                                                                  _letpattern5.0;
                                                              let res3: bool =
                                                                  crate::cbordetver::cbor_det_serialize_map_insert(
                                                                      out012,
                                                                      size0,
                                                                      size1
                                                                  );
                                                              if res3
                                                              {
                                                                  (&mut psize)[0] = size2;
                                                                  (&mut pcount)[0] =
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
                                                  let res2: bool =
                                                      match c22
                                                      {
                                                          option__COSE_Format_evercddl_everparsenomatch_pretty::Some
                                                          { v: c14 }
                                                          =>
                                                            {
                                                                let count0: u64 = (&pcount)[0];
                                                                let res: bool =
                                                                    if
                                                                    count0 < 18446744073709551615u64
                                                                    {
                                                                        let size0: usize =
                                                                            (&psize)[0];
                                                                        let
                                                                        _letpattern3:
                                                                        (&mut [u8], &mut [u8])
                                                                        =
                                                                            out.split_at_mut(size0);
                                                                        let _out0: &[u8] =
                                                                            _letpattern3.0;
                                                                        let out1: &mut [u8] =
                                                                            _letpattern3.1;
                                                                        let
                                                                        mty:
                                                                        crate::cbordetver::cbor_det_int_kind
                                                                        =
                                                                            crate::cbordetver::cbor_det_int_kind::UInt64;
                                                                        let
                                                                        c3:
                                                                        crate::cbordetveraux::cbor_raw
                                                                        =
                                                                            crate::cbordetver::cbor_det_mk_int64(
                                                                                mty,
                                                                                6u64
                                                                            );
                                                                        let
                                                                        res:
                                                                        crate::cbordetver::option__size_t
                                                                        =
                                                                            crate::cbordetver::cbor_det_serialize(
                                                                                c3,
                                                                                out1
                                                                            );
                                                                        let res0: usize =
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
                                                                        let res12: usize = res0;
                                                                        if res12 > 0usize
                                                                        {
                                                                            let size1: usize =
                                                                                size0.wrapping_add(
                                                                                    res12
                                                                                );
                                                                            let
                                                                            _letpattern4:
                                                                            (&[u8], &[u8])
                                                                            =
                                                                                out.split_at(size1);
                                                                            let _out01: &[u8] =
                                                                                _letpattern4.0;
                                                                            let out2: &[u8] =
                                                                                _letpattern4.1;
                                                                            let res2: usize =
                                                                                serialize_everparsenomatch(
                                                                                    c14,
                                                                                    out2
                                                                                );
                                                                            if res2 > 0usize
                                                                            {
                                                                                let size2: usize =
                                                                                    size1.wrapping_add(
                                                                                        res2
                                                                                    );
                                                                                let
                                                                                _letpattern5:
                                                                                (&mut [u8],
                                                                                &mut [u8])
                                                                                =
                                                                                    out.split_at_mut(
                                                                                        size2
                                                                                    );
                                                                                let
                                                                                out012: &mut [u8]
                                                                                =
                                                                                    _letpattern5.0;
                                                                                let res3: bool =
                                                                                    crate::cbordetver::cbor_det_serialize_map_insert(
                                                                                        out012,
                                                                                        size0,
                                                                                        size1
                                                                                    );
                                                                                if res3
                                                                                {
                                                                                    (&mut psize)[0] =
                                                                                        size2;
                                                                                    (&mut pcount)[0] =
                                                                                        count0.wrapping_add(
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
                                                                    { false };
                                                                res
                                                            },
                                                          option__COSE_Format_evercddl_everparsenomatch_pretty::None
                                                          => true,
                                                          _ => panic!("Incomplete pattern matching")
                                                      };
                                                  res2
                                              }
                                              else
                                              { false }
                                          };
                                      res
                                  },
                                either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_FStar_Pervasives_either··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·::Inr
                                { v: c22 }
                                =>
                                  {
                                      let res: bool =
                                          match c22
                                          {
                                              either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_·FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·::Inl
                                              { v: c12 }
                                              =>
                                                {
                                                    let
                                                    _letpattern20:
                                                    (&[u8],
                                                    option__COSE_Format_evercddl_everparsenomatch_pretty)
                                                    =
                                                        c12;
                                                    let res: bool =
                                                        {
                                                            let c13: &[u8] = _letpattern20.0;
                                                            let
                                                            c23:
                                                            option__COSE_Format_evercddl_everparsenomatch_pretty
                                                            =
                                                                _letpattern20.1;
                                                            let count: u64 = (&pcount)[0];
                                                            let res11: bool =
                                                                if count < 18446744073709551615u64
                                                                {
                                                                    let size0: usize = (&psize)[0];
                                                                    let
                                                                    _letpattern3:
                                                                    (&mut [u8], &mut [u8])
                                                                    =
                                                                        out.split_at_mut(size0);
                                                                    let _out0: &[u8] =
                                                                        _letpattern3.0;
                                                                    let out1: &mut [u8] =
                                                                        _letpattern3.1;
                                                                    let
                                                                    mty:
                                                                    crate::cbordetver::cbor_det_int_kind
                                                                    =
                                                                        crate::cbordetver::cbor_det_int_kind::UInt64;
                                                                    let
                                                                    c3:
                                                                    crate::cbordetveraux::cbor_raw
                                                                    =
                                                                        crate::cbordetver::cbor_det_mk_int64(
                                                                            mty,
                                                                            6u64
                                                                        );
                                                                    let
                                                                    res:
                                                                    crate::cbordetver::option__size_t
                                                                    =
                                                                        crate::cbordetver::cbor_det_serialize(
                                                                            c3,
                                                                            out1
                                                                        );
                                                                    let res0: usize =
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
                                                                    let res11: usize = res0;
                                                                    if res11 > 0usize
                                                                    {
                                                                        let size1: usize =
                                                                            size0.wrapping_add(
                                                                                res11
                                                                            );
                                                                        let
                                                                        _letpattern4:
                                                                        (&mut [u8], &mut [u8])
                                                                        =
                                                                            out.split_at_mut(size1);
                                                                        let _out01: &[u8] =
                                                                            _letpattern4.0;
                                                                        let out2: &mut [u8] =
                                                                            _letpattern4.1;
                                                                        let res2: usize =
                                                                            serialize_bstr(
                                                                                c13,
                                                                                out2
                                                                            );
                                                                        if res2 > 0usize
                                                                        {
                                                                            let size2: usize =
                                                                                size1.wrapping_add(
                                                                                    res2
                                                                                );
                                                                            let
                                                                            _letpattern5:
                                                                            (&mut [u8], &mut [u8])
                                                                            =
                                                                                out.split_at_mut(
                                                                                    size2
                                                                                );
                                                                            let out012: &mut [u8] =
                                                                                _letpattern5.0;
                                                                            let res3: bool =
                                                                                crate::cbordetver::cbor_det_serialize_map_insert(
                                                                                    out012,
                                                                                    size0,
                                                                                    size1
                                                                                );
                                                                            if res3
                                                                            {
                                                                                (&mut psize)[0] =
                                                                                    size2;
                                                                                (&mut pcount)[0] =
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
                                                                { false };
                                                            if res11
                                                            {
                                                                let res2: bool =
                                                                    match c23
                                                                    {
                                                                        option__COSE_Format_evercddl_everparsenomatch_pretty::Some
                                                                        { v: c14 }
                                                                        =>
                                                                          {
                                                                              let count0: u64 =
                                                                                  (&pcount)[0];
                                                                              let res: bool =
                                                                                  if
                                                                                  count0
                                                                                  <
                                                                                  18446744073709551615u64
                                                                                  {
                                                                                      let
                                                                                      size0: usize
                                                                                      =
                                                                                          (&psize)[0];
                                                                                      let
                                                                                      _letpattern3:
                                                                                      (&mut [u8],
                                                                                      &mut [u8])
                                                                                      =
                                                                                          out.split_at_mut(
                                                                                              size0
                                                                                          );
                                                                                      let
                                                                                      _out0: &[u8]
                                                                                      =
                                                                                          _letpattern3.0;
                                                                                      let
                                                                                      out1:
                                                                                      &mut [u8]
                                                                                      =
                                                                                          _letpattern3.1;
                                                                                      let
                                                                                      mty:
                                                                                      crate::cbordetver::cbor_det_int_kind
                                                                                      =
                                                                                          crate::cbordetver::cbor_det_int_kind::UInt64;
                                                                                      let
                                                                                      c3:
                                                                                      crate::cbordetveraux::cbor_raw
                                                                                      =
                                                                                          crate::cbordetver::cbor_det_mk_int64(
                                                                                              mty,
                                                                                              5u64
                                                                                          );
                                                                                      let
                                                                                      res:
                                                                                      crate::cbordetver::option__size_t
                                                                                      =
                                                                                          crate::cbordetver::cbor_det_serialize(
                                                                                              c3,
                                                                                              out1
                                                                                          );
                                                                                      let
                                                                                      res0: usize
                                                                                      =
                                                                                          match res
                                                                                          {
                                                                                              crate::cbordetver::option__size_t::None
                                                                                              =>
                                                                                                0usize,
                                                                                              crate::cbordetver::option__size_t::Some
                                                                                              {
                                                                                                  v:
                                                                                                  r
                                                                                              }
                                                                                              => r,
                                                                                              _ =>
                                                                                                panic!(
                                                                                                    "Incomplete pattern matching"
                                                                                                )
                                                                                          };
                                                                                      let
                                                                                      res12: usize
                                                                                      =
                                                                                          res0;
                                                                                      if
                                                                                      res12 > 0usize
                                                                                      {
                                                                                          let
                                                                                          size1:
                                                                                          usize
                                                                                          =
                                                                                              size0.wrapping_add(
                                                                                                  res12
                                                                                              );
                                                                                          let
                                                                                          _letpattern4:
                                                                                          (&[u8],
                                                                                          &[u8])
                                                                                          =
                                                                                              out.split_at(
                                                                                                  size1
                                                                                              );
                                                                                          let
                                                                                          _out01:
                                                                                          &[u8]
                                                                                          =
                                                                                              _letpattern4.0;
                                                                                          let
                                                                                          out2:
                                                                                          &[u8]
                                                                                          =
                                                                                              _letpattern4.1;
                                                                                          let
                                                                                          res2:
                                                                                          usize
                                                                                          =
                                                                                              serialize_everparsenomatch(
                                                                                                  c14,
                                                                                                  out2
                                                                                              );
                                                                                          if
                                                                                          res2
                                                                                          >
                                                                                          0usize
                                                                                          {
                                                                                              let
                                                                                              size2:
                                                                                              usize
                                                                                              =
                                                                                                  size1.wrapping_add(
                                                                                                      res2
                                                                                                  );
                                                                                              let
                                                                                              _letpattern5:
                                                                                              (&mut
                                                                                              [u8],
                                                                                              &mut
                                                                                              [u8])
                                                                                              =
                                                                                                  out.split_at_mut(
                                                                                                      size2
                                                                                                  );
                                                                                              let
                                                                                              out012:
                                                                                              &mut
                                                                                              [u8]
                                                                                              =
                                                                                                  _letpattern5.0;
                                                                                              let
                                                                                              res3:
                                                                                              bool
                                                                                              =
                                                                                                  crate::cbordetver::cbor_det_serialize_map_insert(
                                                                                                      out012,
                                                                                                      size0,
                                                                                                      size1
                                                                                                  );
                                                                                              if
                                                                                              res3
                                                                                              {
                                                                                                  (&mut
                                                                                                  psize)[0] =
                                                                                                      size2;
                                                                                                  (&mut
                                                                                                  pcount)[0] =
                                                                                                      count0.wrapping_add(
                                                                                                          1u64
                                                                                                      );
                                                                                                  true
                                                                                              }
                                                                                              else
                                                                                              {
                                                                                                  false
                                                                                              }
                                                                                          }
                                                                                          else
                                                                                          { false }
                                                                                      }
                                                                                      else
                                                                                      { false }
                                                                                  }
                                                                                  else
                                                                                  { false };
                                                                              res
                                                                          },
                                                                        option__COSE_Format_evercddl_everparsenomatch_pretty::None
                                                                        => true,
                                                                        _ =>
                                                                          panic!(
                                                                              "Incomplete pattern matching"
                                                                          )
                                                                    };
                                                                res2
                                                            }
                                                            else
                                                            { false }
                                                        };
                                                    res
                                                },
                                              either__·COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·_·FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty·::Inr
                                              { v: c23 }
                                              =>
                                                {
                                                    let
                                                    _letpattern20:
                                                    (option__COSE_Format_evercddl_everparsenomatch_pretty,
                                                    option__COSE_Format_evercddl_everparsenomatch_pretty)
                                                    =
                                                        c23;
                                                    let res: bool =
                                                        {
                                                            let
                                                            c12:
                                                            option__COSE_Format_evercddl_everparsenomatch_pretty
                                                            =
                                                                _letpattern20.0;
                                                            let
                                                            c24:
                                                            option__COSE_Format_evercddl_everparsenomatch_pretty
                                                            =
                                                                _letpattern20.1;
                                                            let res11: bool =
                                                                match c12
                                                                {
                                                                    option__COSE_Format_evercddl_everparsenomatch_pretty::Some
                                                                    { v: c13 }
                                                                    =>
                                                                      {
                                                                          let count: u64 =
                                                                              (&pcount)[0];
                                                                          let res: bool =
                                                                              if
                                                                              count
                                                                              <
                                                                              18446744073709551615u64
                                                                              {
                                                                                  let size0: usize =
                                                                                      (&psize)[0];
                                                                                  let
                                                                                  _letpattern3:
                                                                                  (&mut [u8],
                                                                                  &mut [u8])
                                                                                  =
                                                                                      out.split_at_mut(
                                                                                          size0
                                                                                      );
                                                                                  let _out0: &[u8] =
                                                                                      _letpattern3.0;
                                                                                  let
                                                                                  out1: &mut [u8]
                                                                                  =
                                                                                      _letpattern3.1;
                                                                                  let
                                                                                  mty:
                                                                                  crate::cbordetver::cbor_det_int_kind
                                                                                  =
                                                                                      crate::cbordetver::cbor_det_int_kind::UInt64;
                                                                                  let
                                                                                  c3:
                                                                                  crate::cbordetveraux::cbor_raw
                                                                                  =
                                                                                      crate::cbordetver::cbor_det_mk_int64(
                                                                                          mty,
                                                                                          6u64
                                                                                      );
                                                                                  let
                                                                                  res:
                                                                                  crate::cbordetver::option__size_t
                                                                                  =
                                                                                      crate::cbordetver::cbor_det_serialize(
                                                                                          c3,
                                                                                          out1
                                                                                      );
                                                                                  let res0: usize =
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
                                                                                  let res11: usize =
                                                                                      res0;
                                                                                  if res11 > 0usize
                                                                                  {
                                                                                      let
                                                                                      size1: usize
                                                                                      =
                                                                                          size0.wrapping_add(
                                                                                              res11
                                                                                          );
                                                                                      let
                                                                                      _letpattern4:
                                                                                      (&[u8], &[u8])
                                                                                      =
                                                                                          out.split_at(
                                                                                              size1
                                                                                          );
                                                                                      let
                                                                                      _out01: &[u8]
                                                                                      =
                                                                                          _letpattern4.0;
                                                                                      let
                                                                                      out2: &[u8]
                                                                                      =
                                                                                          _letpattern4.1;
                                                                                      let
                                                                                      res2: usize
                                                                                      =
                                                                                          serialize_everparsenomatch(
                                                                                              c13,
                                                                                              out2
                                                                                          );
                                                                                      if
                                                                                      res2 > 0usize
                                                                                      {
                                                                                          let
                                                                                          size2:
                                                                                          usize
                                                                                          =
                                                                                              size1.wrapping_add(
                                                                                                  res2
                                                                                              );
                                                                                          let
                                                                                          _letpattern5:
                                                                                          (&mut [u8],
                                                                                          &mut [u8])
                                                                                          =
                                                                                              out.split_at_mut(
                                                                                                  size2
                                                                                              );
                                                                                          let
                                                                                          out012:
                                                                                          &mut [u8]
                                                                                          =
                                                                                              _letpattern5.0;
                                                                                          let
                                                                                          res3: bool
                                                                                          =
                                                                                              crate::cbordetver::cbor_det_serialize_map_insert(
                                                                                                  out012,
                                                                                                  size0,
                                                                                                  size1
                                                                                              );
                                                                                          if res3
                                                                                          {
                                                                                              (&mut
                                                                                              psize)[0] =
                                                                                                  size2;
                                                                                              (&mut
                                                                                              pcount)[0] =
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
                                                                              { false };
                                                                          res
                                                                      },
                                                                    option__COSE_Format_evercddl_everparsenomatch_pretty::None
                                                                    => true,
                                                                    _ =>
                                                                      panic!(
                                                                          "Incomplete pattern matching"
                                                                      )
                                                                };
                                                            if res11
                                                            {
                                                                let res2: bool =
                                                                    match c24
                                                                    {
                                                                        option__COSE_Format_evercddl_everparsenomatch_pretty::Some
                                                                        { v: c13 }
                                                                        =>
                                                                          {
                                                                              let count: u64 =
                                                                                  (&pcount)[0];
                                                                              let res: bool =
                                                                                  if
                                                                                  count
                                                                                  <
                                                                                  18446744073709551615u64
                                                                                  {
                                                                                      let
                                                                                      size0: usize
                                                                                      =
                                                                                          (&psize)[0];
                                                                                      let
                                                                                      _letpattern3:
                                                                                      (&mut [u8],
                                                                                      &mut [u8])
                                                                                      =
                                                                                          out.split_at_mut(
                                                                                              size0
                                                                                          );
                                                                                      let
                                                                                      _out0: &[u8]
                                                                                      =
                                                                                          _letpattern3.0;
                                                                                      let
                                                                                      out1:
                                                                                      &mut [u8]
                                                                                      =
                                                                                          _letpattern3.1;
                                                                                      let
                                                                                      mty:
                                                                                      crate::cbordetver::cbor_det_int_kind
                                                                                      =
                                                                                          crate::cbordetver::cbor_det_int_kind::UInt64;
                                                                                      let
                                                                                      c3:
                                                                                      crate::cbordetveraux::cbor_raw
                                                                                      =
                                                                                          crate::cbordetver::cbor_det_mk_int64(
                                                                                              mty,
                                                                                              5u64
                                                                                          );
                                                                                      let
                                                                                      res:
                                                                                      crate::cbordetver::option__size_t
                                                                                      =
                                                                                          crate::cbordetver::cbor_det_serialize(
                                                                                              c3,
                                                                                              out1
                                                                                          );
                                                                                      let
                                                                                      res0: usize
                                                                                      =
                                                                                          match res
                                                                                          {
                                                                                              crate::cbordetver::option__size_t::None
                                                                                              =>
                                                                                                0usize,
                                                                                              crate::cbordetver::option__size_t::Some
                                                                                              {
                                                                                                  v:
                                                                                                  r
                                                                                              }
                                                                                              => r,
                                                                                              _ =>
                                                                                                panic!(
                                                                                                    "Incomplete pattern matching"
                                                                                                )
                                                                                          };
                                                                                      let
                                                                                      res12: usize
                                                                                      =
                                                                                          res0;
                                                                                      if
                                                                                      res12 > 0usize
                                                                                      {
                                                                                          let
                                                                                          size1:
                                                                                          usize
                                                                                          =
                                                                                              size0.wrapping_add(
                                                                                                  res12
                                                                                              );
                                                                                          let
                                                                                          _letpattern4:
                                                                                          (&[u8],
                                                                                          &[u8])
                                                                                          =
                                                                                              out.split_at(
                                                                                                  size1
                                                                                              );
                                                                                          let
                                                                                          _out01:
                                                                                          &[u8]
                                                                                          =
                                                                                              _letpattern4.0;
                                                                                          let
                                                                                          out2:
                                                                                          &[u8]
                                                                                          =
                                                                                              _letpattern4.1;
                                                                                          let
                                                                                          res2:
                                                                                          usize
                                                                                          =
                                                                                              serialize_everparsenomatch(
                                                                                                  c13,
                                                                                                  out2
                                                                                              );
                                                                                          if
                                                                                          res2
                                                                                          >
                                                                                          0usize
                                                                                          {
                                                                                              let
                                                                                              size2:
                                                                                              usize
                                                                                              =
                                                                                                  size1.wrapping_add(
                                                                                                      res2
                                                                                                  );
                                                                                              let
                                                                                              _letpattern5:
                                                                                              (&mut
                                                                                              [u8],
                                                                                              &mut
                                                                                              [u8])
                                                                                              =
                                                                                                  out.split_at_mut(
                                                                                                      size2
                                                                                                  );
                                                                                              let
                                                                                              out012:
                                                                                              &mut
                                                                                              [u8]
                                                                                              =
                                                                                                  _letpattern5.0;
                                                                                              let
                                                                                              res3:
                                                                                              bool
                                                                                              =
                                                                                                  crate::cbordetver::cbor_det_serialize_map_insert(
                                                                                                      out012,
                                                                                                      size0,
                                                                                                      size1
                                                                                                  );
                                                                                              if
                                                                                              res3
                                                                                              {
                                                                                                  (&mut
                                                                                                  psize)[0] =
                                                                                                      size2;
                                                                                                  (&mut
                                                                                                  pcount)[0] =
                                                                                                      count.wrapping_add(
                                                                                                          1u64
                                                                                                      );
                                                                                                  true
                                                                                              }
                                                                                              else
                                                                                              {
                                                                                                  false
                                                                                              }
                                                                                          }
                                                                                          else
                                                                                          { false }
                                                                                      }
                                                                                      else
                                                                                      { false }
                                                                                  }
                                                                                  else
                                                                                  { false };
                                                                              res
                                                                          },
                                                                        option__COSE_Format_evercddl_everparsenomatch_pretty::None
                                                                        => true,
                                                                        _ =>
                                                                          panic!(
                                                                              "Incomplete pattern matching"
                                                                          )
                                                                    };
                                                                res2
                                                            }
                                                            else
                                                            { false }
                                                        };
                                                    res
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          };
                                      res
                                  },
                                _ => panic!("Incomplete pattern matching")
                            };
                        res2
                    }
                    else
                    { false }
                };
            if res1
            {
                let res2: bool =
                    match c2
                    {
                        either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty::Inl
                        { v: c11 }
                        =>
                          {
                              let i: &[(evercddl_label_pretty, crate::cbordetveraux::cbor_raw)] =
                                  c11;
                              let
                              pi: [&[(evercddl_label_pretty, crate::cbordetveraux::cbor_raw)]; 1]
                              =
                                  [i; 1usize];
                              crate::lowstar::ignore::ignore::<&[&[(evercddl_label_pretty,
                              crate::cbordetveraux::cbor_raw)]]>(&pi);
                              let
                              mut
                              pc:
                              [&[(evercddl_label_pretty, crate::cbordetveraux::cbor_raw)]; 1]
                              =
                                  [i; 1usize];
                              let mut pres: [bool; 1] = [true; 1usize];
                              let res: bool = (&pres)[0];
                              let mut cond: bool =
                                  if res
                                  {
                                      let
                                      c3: &[(evercddl_label_pretty, crate::cbordetveraux::cbor_raw)]
                                      =
                                          (&pc)[0];
                                      let em: bool = c3.len() == 0usize;
                                      ! em
                                  }
                                  else
                                  { false };
                              while
                              cond
                              {
                                  let count: u64 = (&pcount)[0];
                                  if count == 18446744073709551615u64
                                  { (&mut pres)[0] = false }
                                  else
                                  {
                                      let count·: u64 = count.wrapping_add(1u64);
                                      let
                                      i1: &[(evercddl_label_pretty, crate::cbordetveraux::cbor_raw)]
                                      =
                                          (&pc)[0];
                                      let
                                      res0: (evercddl_label_pretty, crate::cbordetveraux::cbor_raw)
                                      =
                                          i1[0usize];
                                      let
                                      _letpattern10:
                                      (&[(evercddl_label_pretty, crate::cbordetveraux::cbor_raw)],
                                      &[(evercddl_label_pretty, crate::cbordetveraux::cbor_raw)])
                                      =
                                          i1.split_at(1usize);
                                      let
                                      _letpattern11:
                                      (evercddl_label_pretty, crate::cbordetveraux::cbor_raw)
                                      =
                                          {
                                              let
                                              _il:
                                              &[(evercddl_label_pretty,
                                              crate::cbordetveraux::cbor_raw)]
                                              =
                                                  _letpattern10.0;
                                              let
                                              ir:
                                              &[(evercddl_label_pretty,
                                              crate::cbordetveraux::cbor_raw)]
                                              =
                                                  _letpattern10.1;
                                              let
                                              i·:
                                              &[(evercddl_label_pretty,
                                              crate::cbordetveraux::cbor_raw)]
                                              =
                                                  ir;
                                              (&mut pc)[0] = i·;
                                              res0
                                          };
                                      let ck: evercddl_label_pretty = _letpattern11.0;
                                      let cv: crate::cbordetveraux::cbor_raw = _letpattern11.1;
                                      let size0: usize = (&psize)[0];
                                      let _letpattern2: (&mut [u8], &mut [u8]) =
                                          out.split_at_mut(size0);
                                      let _outl1: &[u8] = _letpattern2.0;
                                      let out1: &mut [u8] = _letpattern2.1;
                                      let sz1: usize = aux_env25_serialize_2(ck, out1);
                                      if sz1 == 0usize
                                      { (&mut pres)[0] = false }
                                      else
                                      {
                                          let
                                          _letpattern3:
                                          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                          =
                                              crate::cbordetver::cbor_det_parse(out1);
                                          match _letpattern3
                                          {
                                              crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                              { v: oo }
                                              =>
                                                {
                                                    let
                                                    _letpattern4:
                                                    (crate::cbordetveraux::cbor_raw, &[u8])
                                                    =
                                                        oo;
                                                    let o: crate::cbordetveraux::cbor_raw =
                                                        _letpattern4.0;
                                                    let _orem: &[u8] = _letpattern4.1;
                                                    let is_except: bool = aux_env25_validate_3(o);
                                                    if is_except
                                                    { (&mut pres)[0] = false }
                                                    else
                                                    {
                                                        let _letpattern5: (&mut [u8], &mut [u8]) =
                                                            out1.split_at_mut(sz1);
                                                        let _outl2: &[u8] = _letpattern5.0;
                                                        let out2: &mut [u8] = _letpattern5.1;
                                                        let sz2: usize =
                                                            aux_env25_serialize_4(cv, out2);
                                                        if sz2 == 0usize
                                                        { (&mut pres)[0] = false }
                                                        else
                                                        {
                                                            let size1: usize =
                                                                size0.wrapping_add(sz1);
                                                            let size2: usize =
                                                                size1.wrapping_add(sz2);
                                                            let
                                                            _letpattern6: (&mut [u8], &mut [u8])
                                                            =
                                                                out.split_at_mut(size2);
                                                            let
                                                            _letpattern60: (&mut [u8], &mut [u8])
                                                            =
                                                                {
                                                                    let s1: &mut [u8] =
                                                                        _letpattern6.0;
                                                                    let s2: &mut [u8] =
                                                                        _letpattern6.1;
                                                                    (s1,s2)
                                                                };
                                                            let outl: &mut [u8] = _letpattern60.0;
                                                            let _outr: &[u8] = _letpattern60.1;
                                                            let inserted: bool =
                                                                crate::cbordetver::cbor_det_serialize_map_insert(
                                                                    outl,
                                                                    size0,
                                                                    size1
                                                                );
                                                            if ! inserted
                                                            { (&mut pres)[0] = false }
                                                            else
                                                            {
                                                                (&mut pcount)[0] = count·;
                                                                (&mut psize)[0] = size2
                                                            }
                                                        }
                                                    }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          }
                                      }
                                  };
                                  let res0: bool = (&pres)[0];
                                  let ite: bool =
                                      if res0
                                      {
                                          let
                                          c3:
                                          &[(evercddl_label_pretty, crate::cbordetveraux::cbor_raw)]
                                          =
                                              (&pc)[0];
                                          let em: bool = c3.len() == 0usize;
                                          ! em
                                      }
                                      else
                                      { false };
                                  cond = ite
                              };
                              let res0: bool = (&pres)[0];
                              let res2: bool = res0;
                              res2
                          },
                        either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty::Inr
                        { v: c21 }
                        =>
                          {
                              let
                              mut
                              pc:
                              [map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty;
                              1]
                              =
                                  [c21; 1usize];
                              let mut pres: [bool; 1] = [true; 1usize];
                              let res: bool = (&pres)[0];
                              let mut cond: bool =
                                  if res
                                  {
                                      let
                                      c3:
                                      map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
                                      =
                                          (&pc)[0];
                                      let
                                      mut
                                      pj:
                                      [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry;
                                      1]
                                      =
                                          [c3.cddl_map_iterator_contents; 1usize];
                                      let mut pres1: [bool; 1] = [true; 1usize];
                                      let res2: bool = (&pres1)[0];
                                      let mut cond: bool =
                                          if res2
                                          {
                                              let
                                              j:
                                              crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                              =
                                                  (&pj)[0];
                                              let test: bool =
                                                  crate::cbordetver::cbor_det_map_iterator_is_empty(
                                                      j
                                                  );
                                              ! test
                                          }
                                          else
                                          { false };
                                      while
                                      cond
                                      {
                                          let elt: crate::cbordetveraux::cbor_map_entry =
                                              crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
                                          let elt_key: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(elt);
                                          let test_key: bool =
                                              (c3.cddl_map_iterator_impl_validate1)(elt_key);
                                          if ! ! test_key
                                          {
                                              let test_ex: bool =
                                                  (c3.cddl_map_iterator_impl_validate_ex)(elt_key);
                                              if ! test_ex
                                              {
                                                  let elt_value: crate::cbordetveraux::cbor_raw =
                                                      crate::cbordetver::cbor_det_map_entry_value(
                                                          elt
                                                      );
                                                  let test_value: bool =
                                                      (c3.cddl_map_iterator_impl_validate2)(
                                                          elt_value
                                                      );
                                                  (&mut pres1)[0] = ! test_value
                                              }
                                          };
                                          let res20: bool = (&pres1)[0];
                                          let ite: bool =
                                              if res20
                                              {
                                                  let
                                                  j:
                                                  crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                                  =
                                                      (&pj)[0];
                                                  let test: bool =
                                                      crate::cbordetver::cbor_det_map_iterator_is_empty(
                                                          j
                                                      );
                                                  ! test
                                              }
                                              else
                                              { false };
                                          cond = ite
                                      };
                                      let em: bool = (&pres1)[0];
                                      ! em
                                  }
                                  else
                                  { false };
                              while
                              cond
                              {
                                  let count: u64 = (&pcount)[0];
                                  if count == 18446744073709551615u64
                                  { (&mut pres)[0] = false }
                                  else
                                  {
                                      let count·: u64 = count.wrapping_add(1u64);
                                      let
                                      i:
                                      map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
                                      =
                                          (&pc)[0];
                                      let
                                      mut
                                      pj:
                                      [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry;
                                      1]
                                      =
                                          [i.cddl_map_iterator_contents; 1usize];
                                      let hd0: crate::cbordetveraux::cbor_map_entry =
                                          crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
                                      let mut phd: [crate::cbordetveraux::cbor_map_entry; 1] =
                                          [hd0; 1usize];
                                      let hd: crate::cbordetveraux::cbor_map_entry = (&phd)[0];
                                      let hd_key: crate::cbordetveraux::cbor_raw =
                                          crate::cbordetver::cbor_det_map_entry_key(hd);
                                      let test_key: bool =
                                          (i.cddl_map_iterator_impl_validate1)(hd_key);
                                      let mut cond0: bool =
                                          if ! test_key
                                          { true }
                                          else
                                          {
                                              let test_ex: bool =
                                                  (i.cddl_map_iterator_impl_validate_ex)(hd_key);
                                              if test_ex
                                              { true }
                                              else
                                              {
                                                  let hd_value: crate::cbordetveraux::cbor_raw =
                                                      crate::cbordetver::cbor_det_map_entry_value(
                                                          hd
                                                      );
                                                  let test_value: bool =
                                                      (i.cddl_map_iterator_impl_validate2)(hd_value);
                                                  ! test_value
                                              }
                                          };
                                      while
                                      cond0
                                      {
                                          let hd1: crate::cbordetveraux::cbor_map_entry =
                                              crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
                                          (&mut phd)[0] = hd1;
                                          let hd2: crate::cbordetveraux::cbor_map_entry = (&phd)[0];
                                          let hd_key0: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(hd2);
                                          let test_key0: bool =
                                              (i.cddl_map_iterator_impl_validate1)(hd_key0);
                                          let ite: bool =
                                              if ! test_key0
                                              { true }
                                              else
                                              {
                                                  let test_ex: bool =
                                                      (i.cddl_map_iterator_impl_validate_ex)(
                                                          hd_key0
                                                      );
                                                  if test_ex
                                                  { true }
                                                  else
                                                  {
                                                      let hd_value: crate::cbordetveraux::cbor_raw =
                                                          crate::cbordetver::cbor_det_map_entry_value(
                                                              hd2
                                                          );
                                                      let test_value: bool =
                                                          (i.cddl_map_iterator_impl_validate2)(
                                                              hd_value
                                                          );
                                                      ! test_value
                                                  }
                                              };
                                          cond0 = ite
                                      };
                                      let hd1: crate::cbordetveraux::cbor_map_entry = (&phd)[0];
                                      let hd_key0: crate::cbordetveraux::cbor_raw =
                                          crate::cbordetver::cbor_det_map_entry_key(hd1);
                                      let hd_key_res: evercddl_label_pretty =
                                          (i.cddl_map_iterator_impl_parse1)(hd_key0);
                                      let hd_value: crate::cbordetveraux::cbor_raw =
                                          crate::cbordetver::cbor_det_map_entry_value(hd1);
                                      let hd_value_res: crate::cbordetveraux::cbor_raw =
                                          (i.cddl_map_iterator_impl_parse2)(hd_value);
                                      let
                                      j:
                                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                      =
                                          (&pj)[0];
                                      let
                                      i·:
                                      map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
                                      =
                                          map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
                                          {
                                              cddl_map_iterator_contents: j,
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
                                      (&mut pc)[0] = i·;
                                      let
                                      _letpattern10:
                                      (evercddl_label_pretty, crate::cbordetveraux::cbor_raw)
                                      =
                                          (hd_key_res,hd_value_res);
                                      let ck: evercddl_label_pretty = _letpattern10.0;
                                      let cv: crate::cbordetveraux::cbor_raw = _letpattern10.1;
                                      let size0: usize = (&psize)[0];
                                      let _letpattern2: (&mut [u8], &mut [u8]) =
                                          out.split_at_mut(size0);
                                      let _outl1: &[u8] = _letpattern2.0;
                                      let out1: &mut [u8] = _letpattern2.1;
                                      let sz1: usize = aux_env25_serialize_2(ck, out1);
                                      if sz1 == 0usize
                                      { (&mut pres)[0] = false }
                                      else
                                      {
                                          let
                                          _letpattern3:
                                          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                          =
                                              crate::cbordetver::cbor_det_parse(out1);
                                          match _letpattern3
                                          {
                                              crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                              { v: oo }
                                              =>
                                                {
                                                    let
                                                    _letpattern4:
                                                    (crate::cbordetveraux::cbor_raw, &[u8])
                                                    =
                                                        oo;
                                                    let o: crate::cbordetveraux::cbor_raw =
                                                        _letpattern4.0;
                                                    let _orem: &[u8] = _letpattern4.1;
                                                    let is_except: bool = aux_env25_validate_3(o);
                                                    if is_except
                                                    { (&mut pres)[0] = false }
                                                    else
                                                    {
                                                        let _letpattern5: (&mut [u8], &mut [u8]) =
                                                            out1.split_at_mut(sz1);
                                                        let _outl2: &[u8] = _letpattern5.0;
                                                        let out2: &mut [u8] = _letpattern5.1;
                                                        let sz2: usize =
                                                            aux_env25_serialize_4(cv, out2);
                                                        if sz2 == 0usize
                                                        { (&mut pres)[0] = false }
                                                        else
                                                        {
                                                            let size1: usize =
                                                                size0.wrapping_add(sz1);
                                                            let size2: usize =
                                                                size1.wrapping_add(sz2);
                                                            let
                                                            _letpattern6: (&mut [u8], &mut [u8])
                                                            =
                                                                out.split_at_mut(size2);
                                                            let
                                                            _letpattern60: (&mut [u8], &mut [u8])
                                                            =
                                                                {
                                                                    let s1: &mut [u8] =
                                                                        _letpattern6.0;
                                                                    let s2: &mut [u8] =
                                                                        _letpattern6.1;
                                                                    (s1,s2)
                                                                };
                                                            let outl: &mut [u8] = _letpattern60.0;
                                                            let _outr: &[u8] = _letpattern60.1;
                                                            let inserted: bool =
                                                                crate::cbordetver::cbor_det_serialize_map_insert(
                                                                    outl,
                                                                    size0,
                                                                    size1
                                                                );
                                                            if ! inserted
                                                            { (&mut pres)[0] = false }
                                                            else
                                                            {
                                                                (&mut pcount)[0] = count·;
                                                                (&mut psize)[0] = size2
                                                            }
                                                        }
                                                    }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          }
                                      }
                                  };
                                  let res0: bool = (&pres)[0];
                                  let ite: bool =
                                      if res0
                                      {
                                          let
                                          c3:
                                          map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
                                          =
                                              (&pc)[0];
                                          let
                                          mut
                                          pj:
                                          [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry;
                                          1]
                                          =
                                              [c3.cddl_map_iterator_contents; 1usize];
                                          let mut pres1: [bool; 1] = [true; 1usize];
                                          let res2: bool = (&pres1)[0];
                                          let mut cond0: bool =
                                              if res2
                                              {
                                                  let
                                                  j:
                                                  crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                                  =
                                                      (&pj)[0];
                                                  let test: bool =
                                                      crate::cbordetver::cbor_det_map_iterator_is_empty(
                                                          j
                                                      );
                                                  ! test
                                              }
                                              else
                                              { false };
                                          while
                                          cond0
                                          {
                                              let elt: crate::cbordetveraux::cbor_map_entry =
                                                  crate::cbordetver::cbor_det_map_iterator_next(
                                                      &mut pj
                                                  );
                                              let elt_key: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_key(elt);
                                              let test_key: bool =
                                                  (c3.cddl_map_iterator_impl_validate1)(elt_key);
                                              if ! ! test_key
                                              {
                                                  let test_ex: bool =
                                                      (c3.cddl_map_iterator_impl_validate_ex)(
                                                          elt_key
                                                      );
                                                  if ! test_ex
                                                  {
                                                      let
                                                      elt_value: crate::cbordetveraux::cbor_raw
                                                      =
                                                          crate::cbordetver::cbor_det_map_entry_value(
                                                              elt
                                                          );
                                                      let test_value: bool =
                                                          (c3.cddl_map_iterator_impl_validate2)(
                                                              elt_value
                                                          );
                                                      (&mut pres1)[0] = ! test_value
                                                  }
                                              };
                                              let res20: bool = (&pres1)[0];
                                              let ite: bool =
                                                  if res20
                                                  {
                                                      let
                                                      j:
                                                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                                      =
                                                          (&pj)[0];
                                                      let test: bool =
                                                          crate::cbordetver::cbor_det_map_iterator_is_empty(
                                                              j
                                                          );
                                                      ! test
                                                  }
                                                  else
                                                  { false };
                                              cond0 = ite
                                          };
                                          let em: bool = (&pres1)[0];
                                          ! em
                                      }
                                      else
                                      { false };
                                  cond = ite
                              };
                              let res0: bool = (&pres)[0];
                              res0
                          },
                        _ => panic!("Incomplete pattern matching")
                    };
                res2
            }
            else
            { false }
        };
    let _bind_c: usize =
        if res
        {
            let size: usize = (&psize)[0];
            let count: u64 = (&pcount)[0];
            crate::cbordetver::cbor_det_serialize_map(count, out, size)
        }
        else
        { 0usize };
    let res0: usize = _bind_c;
    res0
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_header_map_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_header_map_pretty <'a>, &'a [u8]) }
}

pub fn validate_and_parse_header_map <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_header_map_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_header_map_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_header_map(rl);
              if test
              {
                  let x: evercddl_header_map_pretty = parse_header_map(rl);
                  option__·COSE_Format_evercddl_header_map_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_header_map_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn is_empty_iterate_array_aux_env25_type_1(
    i:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env25_type_1_pretty
) ->
    bool
{
    let res: bool =
        crate::cbordetver::cbor_det_array_iterator_is_empty(i.cddl_array_iterator_contents);
    res
}

pub fn next_iterate_array_aux_env25_type_1 <'a>(
    pi:
    &'a mut
    [array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env25_type_1_pretty
    <'a>]
) ->
    evercddl_label_pretty
    <'a>
{
    let
    i:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env25_type_1_pretty
    =
        pi[0];
    let len0: u64 =
        crate::cbordetver::cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
    let mut pj: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [i.cddl_array_iterator_contents; 1usize];
    let _test: bool = (i.cddl_array_iterator_impl_validate)(&mut pj);
    crate::lowstar::ignore::ignore::<bool>(_test);
    let ji: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pj)[0];
    let len1: u64 = crate::cbordetver::cbor_det_array_iterator_length(ji);
    let
    j:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env25_type_1_pretty
    =
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env25_type_1_pretty
        {
            cddl_array_iterator_contents: ji,
            cddl_array_iterator_impl_validate: i.cddl_array_iterator_impl_validate,
            cddl_array_iterator_impl_parse: i.cddl_array_iterator_impl_parse
        };
    pi[0] = j;
    let tri: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(
            i.cddl_array_iterator_contents,
            len0.wrapping_sub(len1)
        );
    let res: evercddl_label_pretty = (i.cddl_array_iterator_impl_parse)(tri);
    res
}

pub fn is_empty_iterate_map_aux_env25_type_2_and_aux_env25_type_4(
    i:
    map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
) ->
    bool
{
    let mut pj: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry; 1] =
        [i.cddl_map_iterator_contents; 1usize];
    let mut pres: [bool; 1] = [true; 1usize];
    let res: bool = (&pres)[0];
    let mut cond: bool =
        if res
        {
            let j: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
                (&pj)[0];
            let test: bool = crate::cbordetver::cbor_det_map_iterator_is_empty(j);
            ! test
        }
        else
        { false };
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
            let test_ex: bool = (i.cddl_map_iterator_impl_validate_ex)(elt_key);
            if ! test_ex
            {
                let elt_value: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_map_entry_value(elt);
                let test_value: bool = (i.cddl_map_iterator_impl_validate2)(elt_value);
                (&mut pres)[0] = ! test_value
            }
        };
        let res0: bool = (&pres)[0];
        let ite: bool =
            if res0
            {
                let j: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
                    (&pj)[0];
                let test: bool = crate::cbordetver::cbor_det_map_iterator_is_empty(j);
                ! test
            }
            else
            { false };
        cond = ite
    };
    (&pres)[0]
}

pub fn next_iterate_map_aux_env25_type_2_and_aux_env25_type_4 <'a>(
    pi:
    &'a mut
    [map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
    <'a>]
) ->
    (evercddl_label_pretty <'a>, crate::cbordetveraux::cbor_raw <'a>)
{
    let
    i:
    map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
    =
        pi[0];
    let mut pj: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry; 1] =
        [i.cddl_map_iterator_contents; 1usize];
    let hd0: crate::cbordetveraux::cbor_map_entry =
        crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
    let mut phd: [crate::cbordetveraux::cbor_map_entry; 1] = [hd0; 1usize];
    let hd: crate::cbordetveraux::cbor_map_entry = (&phd)[0];
    let hd_key: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(hd);
    let test_key: bool = (i.cddl_map_iterator_impl_validate1)(hd_key);
    let mut cond: bool =
        if ! test_key
        { true }
        else
        {
            let test_ex: bool = (i.cddl_map_iterator_impl_validate_ex)(hd_key);
            if test_ex
            { true }
            else
            {
                let hd_value: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_map_entry_value(hd);
                let test_value: bool = (i.cddl_map_iterator_impl_validate2)(hd_value);
                ! test_value
            }
        };
    while
    cond
    {
        let hd1: crate::cbordetveraux::cbor_map_entry =
            crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
        (&mut phd)[0] = hd1;
        let hd2: crate::cbordetveraux::cbor_map_entry = (&phd)[0];
        let hd_key0: crate::cbordetveraux::cbor_raw =
            crate::cbordetver::cbor_det_map_entry_key(hd2);
        let test_key0: bool = (i.cddl_map_iterator_impl_validate1)(hd_key0);
        let ite: bool =
            if ! test_key0
            { true }
            else
            {
                let test_ex: bool = (i.cddl_map_iterator_impl_validate_ex)(hd_key0);
                if test_ex
                { true }
                else
                {
                    let hd_value: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_map_entry_value(hd2);
                    let test_value: bool = (i.cddl_map_iterator_impl_validate2)(hd_value);
                    ! test_value
                }
            };
        cond = ite
    };
    let hd1: crate::cbordetveraux::cbor_map_entry = (&phd)[0];
    let hd_key0: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(hd1);
    let hd_key_res: evercddl_label_pretty = (i.cddl_map_iterator_impl_parse1)(hd_key0);
    let hd_value: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_map_entry_value(hd1);
    let hd_value_res: crate::cbordetveraux::cbor_raw = (i.cddl_map_iterator_impl_parse2)(hd_value);
    let j: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry = (&pj)[0];
    let
    i·:
    map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
    =
        map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
        {
            cddl_map_iterator_contents: j,
            cddl_map_iterator_impl_validate1: i.cddl_map_iterator_impl_validate1,
            cddl_map_iterator_impl_parse1: i.cddl_map_iterator_impl_parse1,
            cddl_map_iterator_impl_validate_ex: i.cddl_map_iterator_impl_validate_ex,
            cddl_map_iterator_impl_validate2: i.cddl_map_iterator_impl_validate2,
            cddl_map_iterator_impl_parse2: i.cddl_map_iterator_impl_parse2
        };
    pi[0] = i·;
    (hd_key_res,hd_value_res)
}

pub fn validate_empty_or_serialized_map(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    let test: bool = mt == crate::cbordetveraux::cbor_major_type_byte_string;
    let test0: bool =
        if test
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern: crate::cbordetver::cbor_det_view = v1;
            let pl: &[u8] =
                match _letpattern
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
                      let _letpattern0: (crate::cbordetveraux::cbor_raw, &[u8]) = r;
                      let res: crate::cbordetveraux::cbor_raw = _letpattern0.0;
                      let rem: &[u8] = _letpattern0.1;
                      if rem.len() == 0usize
                      {
                          let tres: bool = validate_header_map(res);
                          tres
                      }
                      else
                      { false }
                  },
                _ => panic!("Incomplete pattern matching")
            }
        }
        else
        { false };
    if test0
    { true }
    else
    {
        let mt0: u8 = crate::cbordetver::cbor_det_major_type(c);
        if mt0 == 2u8
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern: crate::cbordetver::cbor_det_view = v1;
            let str: &[u8] =
                match _letpattern
                {
                    crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let len: usize = str.len();
            0usize <= len && len <= 0usize
        }
        else
        { false }
    }
}

#[derive(PartialEq, Clone, Copy)]
enum evercddl_empty_or_serialized_map <'a>
{
    Inl { v: evercddl_header_map_pretty <'a> },
    Inr { v: &'a [u8] }
}

#[derive(PartialEq, Clone, Copy)]
enum evercddl_empty_or_serialized_map_pretty_tags
{
    Mkevercddl_empty_or_serialized_map_pretty0,
    Mkevercddl_empty_or_serialized_map_pretty1
}

#[derive(PartialEq, Clone, Copy)]
pub enum evercddl_empty_or_serialized_map_pretty <'a>
{
    Mkevercddl_empty_or_serialized_map_pretty0 { _x0: evercddl_header_map_pretty <'a> },
    Mkevercddl_empty_or_serialized_map_pretty1 { _x0: &'a [u8] }
}

pub fn uu___is_Mkevercddl_empty_or_serialized_map_pretty0(
    projectee: evercddl_empty_or_serialized_map_pretty
) ->
    bool
{
    match projectee
    {
        evercddl_empty_or_serialized_map_pretty::Mkevercddl_empty_or_serialized_map_pretty0
        { .. }
        => true,
        _ => false
    }
}

pub fn uu___is_Mkevercddl_empty_or_serialized_map_pretty1(
    projectee: evercddl_empty_or_serialized_map_pretty
) ->
    bool
{
    match projectee
    {
        evercddl_empty_or_serialized_map_pretty::Mkevercddl_empty_or_serialized_map_pretty1
        { .. }
        => true,
        _ => false
    }
}

fn evercddl_empty_or_serialized_map_pretty_right <'a>(
    x2: evercddl_empty_or_serialized_map <'a>
) ->
    evercddl_empty_or_serialized_map_pretty
    <'a>
{
    match x2
    {
        evercddl_empty_or_serialized_map::Inl { v: x3 } =>
          evercddl_empty_or_serialized_map_pretty::Mkevercddl_empty_or_serialized_map_pretty0
          { _x0: x3 },
        evercddl_empty_or_serialized_map::Inr { v: x4 } =>
          evercddl_empty_or_serialized_map_pretty::Mkevercddl_empty_or_serialized_map_pretty1
          { _x0: x4 },
        _ => panic!("Incomplete pattern matching")
    }
}

fn evercddl_empty_or_serialized_map_pretty_left <'a>(
    x7: evercddl_empty_or_serialized_map_pretty <'a>
) ->
    evercddl_empty_or_serialized_map
    <'a>
{
    match x7
    {
        evercddl_empty_or_serialized_map_pretty::Mkevercddl_empty_or_serialized_map_pretty0
        { _x0: x10 }
        => evercddl_empty_or_serialized_map::Inl { v: x10 },
        evercddl_empty_or_serialized_map_pretty::Mkevercddl_empty_or_serialized_map_pretty1
        { _x0: x12 }
        => evercddl_empty_or_serialized_map::Inr { v: x12 },
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
Parser for evercddl_empty_or_serialized_map
*/
pub fn
parse_empty_or_serialized_map
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_empty_or_serialized_map_pretty
    <'a>
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    let test: bool = mt == crate::cbordetveraux::cbor_major_type_byte_string;
    let test0: bool =
        if test
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern: crate::cbordetver::cbor_det_view = v1;
            let pl: &[u8] =
                match _letpattern
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
                      let _letpattern0: (crate::cbordetveraux::cbor_raw, &[u8]) = r;
                      let res: crate::cbordetveraux::cbor_raw = _letpattern0.0;
                      let rem: &[u8] = _letpattern0.1;
                      if rem.len() == 0usize
                      {
                          let tres: bool = validate_header_map(res);
                          tres
                      }
                      else
                      { false }
                  },
                _ => panic!("Incomplete pattern matching")
            }
        }
        else
        { false };
    let res1: evercddl_empty_or_serialized_map =
        if test0
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern: crate::cbordetver::cbor_det_view = v1;
            let cs: &[u8] =
                match _letpattern
                {
                    crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let
            cp:
            crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
            =
                crate::cbordetver::cbor_det_parse(cs);
            let res: evercddl_header_map_pretty =
                match cp
                {
                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                    { v: cp_ }
                    =>
                      {
                          let cp1: crate::cbordetveraux::cbor_raw =
                              fst__CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice·uint8_t(cp_);
                          let res: evercddl_header_map_pretty = parse_header_map(cp1);
                          res
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            evercddl_empty_or_serialized_map::Inl { v: res }
        }
        else
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern: crate::cbordetver::cbor_det_view = v1;
            let s: &[u8] =
                match _letpattern
                {
                    crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let res: &[u8] = s;
            evercddl_empty_or_serialized_map::Inr { v: res }
        };
    let res2: evercddl_empty_or_serialized_map_pretty =
        evercddl_empty_or_serialized_map_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_empty_or_serialized_map
*/
pub fn
serialize_empty_or_serialized_map(c: evercddl_empty_or_serialized_map_pretty, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_empty_or_serialized_map = evercddl_empty_or_serialized_map_pretty_left(c);
    match c·
    {
        evercddl_empty_or_serialized_map::Inl { v: c1 } =>
          {
              let sz: usize = serialize_header_map(c1, out);
              if sz == 0usize || sz > 18446744073709551615u64 as usize
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
        evercddl_empty_or_serialized_map::Inr { v: c2 } =>
          {
              let len: usize = c2.len();
              if 0u64 as usize <= len && len <= 0u64 as usize
              {
                  if 2u8 == crate::cbordetveraux::cbor_major_type_byte_string
                  {
                      let len1: usize = c2.len();
                      if len1 <= 18446744073709551615u64 as usize
                      {
                          let mty: crate::cbordetver::cbor_det_string_kind =
                              crate::cbordetver::cbor_det_string_kind::ByteString;
                          let res: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                              crate::cbordetver::cbor_det_mk_string(mty, c2);
                          let _letpattern: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                              res;
                          let x: crate::cbordetveraux::cbor_raw =
                              match _letpattern
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
                      if len1 <= 18446744073709551615u64 as usize
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
                              let
                              _letpattern: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                              =
                                  res;
                              let x: crate::cbordetveraux::cbor_raw =
                                  match _letpattern
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

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_empty_or_serialized_map_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_empty_or_serialized_map_pretty <'a>, &'a [u8]) }
}

pub fn validate_and_parse_empty_or_serialized_map <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_empty_or_serialized_map_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_empty_or_serialized_map_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_empty_or_serialized_map(rl);
              if test
              {
                  let x: evercddl_empty_or_serialized_map_pretty =
                      parse_empty_or_serialized_map(rl);
                  option__·COSE_Format_evercddl_empty_or_serialized_map_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_empty_or_serialized_map_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_COSE_Signature(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let ty: u8 = crate::cbordetver::cbor_det_major_type(c);
    if ty == crate::cbordetveraux::cbor_major_type_array
    {
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Array { _0: a } =>
                  {
                      let
                      res: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                      =
                          crate::cbordetver::cbor_det_array_iterator_start(a);
                      res
                  },
                _ => panic!("Incomplete pattern matching")
            };
        let mut pi: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
            [i; 1usize];
        let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pi)[0];
        let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
        let test1: bool =
            if is_done
            { false }
            else
            {
                let c1: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                let test: bool = validate_empty_or_serialized_map(c1);
                test
            };
        let test10: bool =
            if test1
            {
                let i10: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0];
                let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i10);
                let test2: bool =
                    if is_done0
                    { false }
                    else
                    {
                        let c1: crate::cbordetveraux::cbor_raw =
                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                        let test: bool = validate_header_map(c1);
                        test
                    };
                test2
            }
            else
            { false };
        let b_success: bool =
            if test10
            {
                let i10: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0];
                let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i10);
                let test2: bool =
                    if is_done0
                    { false }
                    else
                    {
                        let c1: crate::cbordetveraux::cbor_raw =
                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                        let test: bool = validate_bstr(c1);
                        test
                    };
                test2
            }
            else
            { false };
        if b_success
        {
            let i·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pi)[0];
            let b_end: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i·);
            b_end
        }
        else
        { false }
    }
    else
    { false }
}

#[derive(PartialEq, Clone, Copy)]
pub struct evercddl_COSE_Signature_pretty <'a>
{
    pub protected: evercddl_empty_or_serialized_map_pretty <'a>,
    pub unprotected: evercddl_header_map_pretty <'a>,
    pub signature: &'a [u8]
}

pub fn uu___is_Mkevercddl_COSE_Signature_pretty0(projectee: evercddl_COSE_Signature_pretty) ->
    bool
{
    crate::lowstar::ignore::ignore::<evercddl_COSE_Signature_pretty>(projectee);
    true
}

fn evercddl_COSE_Signature_pretty_right <'a>(
    x3: ((evercddl_empty_or_serialized_map_pretty <'a>, evercddl_header_map_pretty <'a>), &'a [u8])
) ->
    evercddl_COSE_Signature_pretty
    <'a>
{
    match x3
    {
        ((x4,x5),x6) =>
          evercddl_COSE_Signature_pretty { protected: x4, unprotected: x5, signature: x6 }
    }
}

fn evercddl_COSE_Signature_pretty_left <'a>(x7: evercddl_COSE_Signature_pretty <'a>) ->
    ((evercddl_empty_or_serialized_map_pretty <'a>, evercddl_header_map_pretty <'a>), &'a [u8])
{
    let x12: evercddl_empty_or_serialized_map_pretty = x7.protected;
    let x13: evercddl_header_map_pretty = x7.unprotected;
    let x14: &[u8] = x7.signature;
    ((x12,x13),x14)
}

/**
Parser for evercddl_COSE_Signature
*/
pub fn
parse_COSE_Signature
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_COSE_Signature_pretty
    <'a>
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let ar: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Array { _0: a } =>
              {
                  let res: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                      crate::cbordetver::cbor_det_array_iterator_start(a);
                  res
              },
            _ => panic!("Incomplete pattern matching")
        };
    let rlen0: u64 = crate::cbordetver::cbor_det_array_iterator_length(ar);
    let mut pc: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [ar; 1usize];
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0];
    let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i);
    let test1: bool =
        if is_done
        { false }
        else
        {
            let c1: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
            let test: bool = validate_empty_or_serialized_map(c1);
            test
        };
    let _tmp: bool =
        if test1
        {
            let i0: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc)[0];
            let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i0);
            let test2: bool =
                if is_done0
                { false }
                else
                {
                    let c1: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
                    let test: bool = validate_header_map(c1);
                    test
                };
            test2
        }
        else
        { false };
    crate::lowstar::ignore::ignore::<bool>(_tmp);
    let c1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0];
    let rlen1: u64 = crate::cbordetver::cbor_det_array_iterator_length(c1);
    let c0·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(ar, rlen0.wrapping_sub(rlen1));
    let rlen01: u64 = crate::cbordetver::cbor_det_array_iterator_length(c0·);
    let mut pc1: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·; 1usize];
    let i0: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc1)[0];
    let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i0);
    let _tmp1: bool =
        if is_done0
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc1);
            let test: bool = validate_empty_or_serialized_map(c2);
            test
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp1);
    let c11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc1)[0];
    let rlen11: u64 = crate::cbordetver::cbor_det_array_iterator_length(c11);
    let c0·1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c0·, rlen01.wrapping_sub(rlen11));
    let mut pc2: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·1; 1usize];
    let x: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc2);
    let res: evercddl_empty_or_serialized_map_pretty = parse_empty_or_serialized_map(x);
    let w1: evercddl_empty_or_serialized_map_pretty = res;
    let mut pc20: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c11; 1usize];
    let x0: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc20);
    let res0: evercddl_header_map_pretty = parse_header_map(x0);
    let w2: evercddl_header_map_pretty = res0;
    let w10: (evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty) = (w1,w2);
    let mut pc10: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c1; 1usize];
    let x1: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc10);
    let res1: &[u8] = parse_bstr(x1);
    let w20: &[u8] = res1;
    let res2: ((evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty), &[u8]) =
        (w10,w20);
    let res10: ((evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty), &[u8]) =
        res2;
    let res20: evercddl_COSE_Signature_pretty = evercddl_COSE_Signature_pretty_right(res10);
    res20
}

/**
Serializer for evercddl_COSE_Signature
*/
pub fn
serialize_COSE_Signature(c: evercddl_COSE_Signature_pretty, out: &mut [u8]) ->
    usize
{
    let c·: ((evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty), &[u8]) =
        evercddl_COSE_Signature_pretty_left(c);
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let
    _letpattern: ((evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty), &[u8])
    =
        c·;
    let res: bool =
        {
            let c1: (evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty) =
                _letpattern.0;
            let c2: &[u8] = _letpattern.1;
            let
            _letpattern1: (evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty)
            =
                c1;
            let res1: bool =
                {
                    let c11: evercddl_empty_or_serialized_map_pretty = _letpattern1.0;
                    let c21: evercddl_header_map_pretty = _letpattern1.1;
                    let count: u64 = (&pcount)[0];
                    let res1: bool =
                        if count < 18446744073709551615u64
                        {
                            let size: usize = (&psize)[0];
                            let _letpattern2: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                            let _out0: &[u8] = _letpattern2.0;
                            let out1: &mut [u8] = _letpattern2.1;
                            let size1: usize = serialize_empty_or_serialized_map(c11, out1);
                            if size1 == 0usize
                            { false }
                            else
                            {
                                (&mut pcount)[0] = count.wrapping_add(1u64);
                                (&mut psize)[0] = size.wrapping_add(size1);
                                true
                            }
                        }
                        else
                        { false };
                    if res1
                    {
                        let count0: u64 = (&pcount)[0];
                        let res2: bool =
                            if count0 < 18446744073709551615u64
                            {
                                let size: usize = (&psize)[0];
                                let _letpattern2: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                                let _out0: &[u8] = _letpattern2.0;
                                let out1: &mut [u8] = _letpattern2.1;
                                let size1: usize = serialize_header_map(c21, out1);
                                if size1 == 0usize
                                { false }
                                else
                                {
                                    (&mut pcount)[0] = count0.wrapping_add(1u64);
                                    (&mut psize)[0] = size.wrapping_add(size1);
                                    true
                                }
                            }
                            else
                            { false };
                        res2
                    }
                    else
                    { false }
                };
            if res1
            {
                let count: u64 = (&pcount)[0];
                let res2: bool =
                    if count < 18446744073709551615u64
                    {
                        let size: usize = (&psize)[0];
                        let _letpattern10: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                        let _out0: &[u8] = _letpattern10.0;
                        let out1: &mut [u8] = _letpattern10.1;
                        let size1: usize = serialize_bstr(c2, out1);
                        if size1 == 0usize
                        { false }
                        else
                        {
                            (&mut pcount)[0] = count.wrapping_add(1u64);
                            (&mut psize)[0] = size.wrapping_add(size1);
                            true
                        }
                    }
                    else
                    { false };
                res2
            }
            else
            { false }
        };
    let _bind_c: usize =
        if res
        {
            let size: usize = (&psize)[0];
            let count: u64 = (&pcount)[0];
            crate::cbordetver::cbor_det_serialize_array(count, out, size)
        }
        else
        { 0usize };
    let res0: usize = _bind_c;
    res0
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_COSE_Signature_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_COSE_Signature_pretty <'a>, &'a [u8]) }
}

pub fn validate_and_parse_COSE_Signature <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_COSE_Signature_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_COSE_Signature_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_COSE_Signature(rl);
              if test
              {
                  let x: evercddl_COSE_Signature_pretty = parse_COSE_Signature(rl);
                  option__·COSE_Format_evercddl_COSE_Signature_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_COSE_Signature_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn aux_env29_validate_1(
    pi: &mut [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw]
) ->
    bool
{
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = pi[0];
    let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i);
    if is_done
    { false }
    else
    {
        let c: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_array_iterator_next(pi);
        let test: bool = validate_COSE_Signature(c);
        test
    }
}

pub type aux_env29_type_1_pretty <'a> = evercddl_COSE_Signature_pretty <'a>;

pub fn uu___is_Mkaux_env29_type_1_pretty0(projectee: evercddl_COSE_Signature_pretty) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_COSE_Signature_pretty>(projectee);
    true
}

fn aux_env29_type_1_pretty_right <'a>(x1: evercddl_COSE_Signature_pretty <'a>) ->
    evercddl_COSE_Signature_pretty
    <'a>
{ x1 }

fn aux_env29_type_1_pretty_left <'a>(x3: evercddl_COSE_Signature_pretty <'a>) ->
    evercddl_COSE_Signature_pretty
    <'a>
{ x3 }

/**
Parser for aux_env29_type_1
*/
pub fn
aux_env29_parse_1
<'a>(c: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>) ->
    evercddl_COSE_Signature_pretty
    <'a>
{
    let mut pc: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c; 1usize];
    let x: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
    let res: evercddl_COSE_Signature_pretty = parse_COSE_Signature(x);
    let res1: evercddl_COSE_Signature_pretty = res;
    let res2: evercddl_COSE_Signature_pretty = aux_env29_type_1_pretty_right(res1);
    res2
}

/**
Serializer for aux_env29_type_1
*/
pub fn
aux_env29_serialize_1(
    c: evercddl_COSE_Signature_pretty,
    out: &mut [u8],
    out_count: &mut [u64],
    out_size: &mut [usize]
) ->
    bool
{
    let c·: evercddl_COSE_Signature_pretty = aux_env29_type_1_pretty_left(c);
    let count: u64 = out_count[0];
    if count < 18446744073709551615u64
    {
        let size: usize = out_size[0];
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
        let _out0: &[u8] = _letpattern.0;
        let out1: &mut [u8] = _letpattern.1;
        let size1: usize = serialize_COSE_Signature(c·, out1);
        if size1 == 0usize
        { false }
        else
        {
            out_count[0] = count.wrapping_add(1u64);
            out_size[0] = size.wrapping_add(size1);
            true
        }
    }
    else
    { false }
}

pub fn validate_COSE_Sign(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let ty: u8 = crate::cbordetver::cbor_det_major_type(c);
    if ty == crate::cbordetveraux::cbor_major_type_array
    {
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Array { _0: a } =>
                  {
                      let
                      res: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                      =
                          crate::cbordetver::cbor_det_array_iterator_start(a);
                      res
                  },
                _ => panic!("Incomplete pattern matching")
            };
        let mut pi: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
            [i; 1usize];
        let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pi)[0];
        let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
        let test1: bool =
            if is_done
            { false }
            else
            {
                let c1: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                let test: bool = validate_empty_or_serialized_map(c1);
                test
            };
        let test10: bool =
            if test1
            {
                let i10: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0];
                let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i10);
                let test2: bool =
                    if is_done0
                    { false }
                    else
                    {
                        let c1: crate::cbordetveraux::cbor_raw =
                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                        let test: bool = validate_header_map(c1);
                        test
                    };
                test2
            }
            else
            { false };
        let b_success: bool =
            if test10
            {
                let i10: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0];
                let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i10);
                let test11: bool =
                    if is_done0
                    { false }
                    else
                    {
                        let c1: crate::cbordetveraux::cbor_raw =
                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                        let test: bool = validate_bstr(c1);
                        let test0: bool = if test { true } else { validate_nil(c1) };
                        test0
                    };
                let test2: bool =
                    if test11
                    {
                        let
                        i11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                        =
                            (&pi)[0];
                        let is_done1: bool =
                            crate::cbordetver::cbor_det_array_iterator_is_empty(i11);
                        let test2: bool =
                            if is_done1
                            { false }
                            else
                            {
                                let c1: crate::cbordetveraux::cbor_raw =
                                    crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                let ty1: u8 = crate::cbordetver::cbor_det_major_type(c1);
                                let test: bool =
                                    if ty1 == crate::cbordetveraux::cbor_major_type_array
                                    {
                                        let v10: crate::cbordetver::cbor_det_view =
                                            crate::cbordetver::cbor_det_destruct(c1);
                                        let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                                        let
                                        i2:
                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                        =
                                            match _letpattern0
                                            {
                                                crate::cbordetver::cbor_det_view::Array { _0: a } =>
                                                  {
                                                      let
                                                      res:
                                                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                      =
                                                          crate::cbordetver::cbor_det_array_iterator_start(
                                                              a
                                                          );
                                                      res
                                                  },
                                                _ => panic!("Incomplete pattern matching")
                                            };
                                        let
                                        mut
                                        pi1:
                                        [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw;
                                        1]
                                        =
                                            [i2; 1usize];
                                        let
                                        i3:
                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                        =
                                            (&pi1)[0];
                                        let is_done10: bool =
                                            crate::cbordetver::cbor_det_array_iterator_is_empty(i3);
                                        let test12: bool =
                                            if is_done10
                                            { false }
                                            else
                                            {
                                                let c2: crate::cbordetveraux::cbor_raw =
                                                    crate::cbordetver::cbor_det_array_iterator_next(
                                                        &mut pi1
                                                    );
                                                let test: bool = validate_COSE_Signature(c2);
                                                test
                                            };
                                        let b_success: bool =
                                            if test12
                                            {
                                                let mut pcont: [bool; 1] = [true; 1usize];
                                                while
                                                (&pcont)[0]
                                                {
                                                    let
                                                    i110:
                                                    crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                    =
                                                        (&pi1)[0];
                                                    let
                                                    i30:
                                                    crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                    =
                                                        (&pi1)[0];
                                                    let is_done11: bool =
                                                        crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                            i30
                                                        );
                                                    let cont: bool =
                                                        if is_done11
                                                        { false }
                                                        else
                                                        {
                                                            let c2: crate::cbordetveraux::cbor_raw =
                                                                crate::cbordetver::cbor_det_array_iterator_next(
                                                                    &mut pi1
                                                                );
                                                            let test: bool =
                                                                validate_COSE_Signature(c2);
                                                            test
                                                        };
                                                    if ! cont
                                                    {
                                                        (&mut pi1)[0] = i110;
                                                        (&mut pcont)[0] = false
                                                    }
                                                };
                                                let test2: bool = true;
                                                test2
                                            }
                                            else
                                            { false };
                                        let _bind_c: bool =
                                            if b_success
                                            {
                                                let
                                                i·:
                                                crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                =
                                                    (&pi1)[0];
                                                let b_end: bool =
                                                    crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                        i·
                                                    );
                                                b_end
                                            }
                                            else
                                            { false };
                                        _bind_c
                                    }
                                    else
                                    { false };
                                test
                            };
                        test2
                    }
                    else
                    { false };
                test2
            }
            else
            { false };
        if b_success
        {
            let i·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pi)[0];
            let b_end: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i·);
            b_end
        }
        else
        { false }
    }
    else
    { false }
}

#[derive(PartialEq, Clone, Copy)]
pub enum either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty <'a>
{
    Inl { v: &'a [u8] },
    Inr { v: evercddl_nil_pretty }
}

#[derive(PartialEq, Clone, Copy)]
pub struct
array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1_pretty
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
    evercddl_COSE_Signature_pretty
    <'a1>
}

#[derive(PartialEq, Clone, Copy)]
pub enum
either__CDDL_Pulse_Types_slice·COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env29_type_1_pretty
<'a>
{
    Inl { v: &'a [evercddl_COSE_Signature_pretty <'a>] },
    Inr
    {
        v:
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1_pretty
        <'a>
    }
}

#[derive(PartialEq, Clone, Copy)]
pub struct evercddl_COSE_Sign_pretty <'a>
{
    pub protected: evercddl_empty_or_serialized_map_pretty <'a>,
    pub unprotected: evercddl_header_map_pretty <'a>,
    pub payload: either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty <'a>,
    pub signatures:
    either__CDDL_Pulse_Types_slice·COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env29_type_1_pretty
    <'a>
}

pub fn uu___is_Mkevercddl_COSE_Sign_pretty0(projectee: evercddl_COSE_Sign_pretty) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_COSE_Sign_pretty>(projectee);
    true
}

fn evercddl_COSE_Sign_pretty_right <'a>(
    x4:
    ((evercddl_empty_or_serialized_map_pretty <'a>, evercddl_header_map_pretty <'a>),
    (either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
    <'a>,
    either__CDDL_Pulse_Types_slice·COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env29_type_1_pretty
    <'a>))
) ->
    evercddl_COSE_Sign_pretty
    <'a>
{
    match x4
    {
        ((x5,x6),(x7,x8)) =>
          evercddl_COSE_Sign_pretty { protected: x5, unprotected: x6, payload: x7, signatures: x8 }
    }
}

fn evercddl_COSE_Sign_pretty_left <'a>(x9: evercddl_COSE_Sign_pretty <'a>) ->
    ((evercddl_empty_or_serialized_map_pretty <'a>, evercddl_header_map_pretty <'a>),
    (either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
    <'a>,
    either__CDDL_Pulse_Types_slice·COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env29_type_1_pretty
    <'a>))
{
    let x15: evercddl_empty_or_serialized_map_pretty = x9.protected;
    let x16: evercddl_header_map_pretty = x9.unprotected;
    let x17: either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty = x9.payload;
    let
    x18:
    either__CDDL_Pulse_Types_slice·COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env29_type_1_pretty
    =
        x9.signatures;
    ((x15,x16),(x17,x18))
}

/**
Parser for evercddl_COSE_Sign
*/
pub fn
parse_COSE_Sign
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_COSE_Sign_pretty
    <'a>
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let ar: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Array { _0: a } =>
              {
                  let res: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                      crate::cbordetver::cbor_det_array_iterator_start(a);
                  res
              },
            _ => panic!("Incomplete pattern matching")
        };
    let rlen0: u64 = crate::cbordetver::cbor_det_array_iterator_length(ar);
    let mut pc: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [ar; 1usize];
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0];
    let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i);
    let test1: bool =
        if is_done
        { false }
        else
        {
            let c1: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
            let test: bool = validate_empty_or_serialized_map(c1);
            test
        };
    let _tmp: bool =
        if test1
        {
            let i0: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc)[0];
            let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i0);
            let test2: bool =
                if is_done0
                { false }
                else
                {
                    let c1: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
                    let test: bool = validate_header_map(c1);
                    test
                };
            test2
        }
        else
        { false };
    crate::lowstar::ignore::ignore::<bool>(_tmp);
    let c1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0];
    let rlen1: u64 = crate::cbordetver::cbor_det_array_iterator_length(c1);
    let c0·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(ar, rlen0.wrapping_sub(rlen1));
    let rlen01: u64 = crate::cbordetver::cbor_det_array_iterator_length(c0·);
    let mut pc1: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·; 1usize];
    let i0: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc1)[0];
    let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i0);
    let _tmp1: bool =
        if is_done0
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc1);
            let test: bool = validate_empty_or_serialized_map(c2);
            test
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp1);
    let c11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc1)[0];
    let rlen11: u64 = crate::cbordetver::cbor_det_array_iterator_length(c11);
    let c0·1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c0·, rlen01.wrapping_sub(rlen11));
    let mut pc2: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·1; 1usize];
    let x: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc2);
    let res: evercddl_empty_or_serialized_map_pretty = parse_empty_or_serialized_map(x);
    let w1: evercddl_empty_or_serialized_map_pretty = res;
    let mut pc20: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c11; 1usize];
    let x0: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc20);
    let res0: evercddl_header_map_pretty = parse_header_map(x0);
    let w2: evercddl_header_map_pretty = res0;
    let w10: (evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty) = (w1,w2);
    let rlen010: u64 = crate::cbordetver::cbor_det_array_iterator_length(c1);
    let mut pc10: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c1; 1usize];
    let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc10)[0];
    let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
    let _tmp10: bool =
        if is_done1
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc10);
            let test: bool = validate_bstr(c2);
            let test0: bool = if test { true } else { validate_nil(c2) };
            test0
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp10);
    let c110: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc10)[0];
    let rlen110: u64 = crate::cbordetver::cbor_det_array_iterator_length(c110);
    let c0·10: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c1, rlen010.wrapping_sub(rlen110));
    let mut pc21: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·10; 1usize];
    let x1: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc21);
    let test: bool = validate_bstr(x1);
    let res1: either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty =
        if test
        {
            let res1: &[u8] = parse_bstr(x1);
            either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty::Inl
            { v: res1 }
        }
        else
        {
            let res1: evercddl_nil_pretty = parse_nil(x1);
            either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty::Inr
            { v: res1 }
        };
    let w11: either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty = res1;
    let mut pc22: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c110; 1usize];
    let x2: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc22);
    let v10: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(x2);
    let _letpattern0: crate::cbordetver::cbor_det_view = v10;
    let ar1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern0
        {
            crate::cbordetver::cbor_det_view::Array { _0: a } =>
              {
                  let res2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                      crate::cbordetver::cbor_det_array_iterator_start(a);
                  res2
              },
            _ => panic!("Incomplete pattern matching")
        };
    let
    i2:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1_pretty
    =
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1_pretty
        {
            cddl_array_iterator_contents: ar1,
            cddl_array_iterator_impl_validate: aux_env29_validate_1,
            cddl_array_iterator_impl_parse: aux_env29_parse_1
        };
    let
    res2:
    either__CDDL_Pulse_Types_slice·COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env29_type_1_pretty
    =
        either__CDDL_Pulse_Types_slice·COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env29_type_1_pretty::Inr
        { v: i2 };
    let
    w20:
    either__CDDL_Pulse_Types_slice·COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env29_type_1_pretty
    =
        res2;
    let
    w21:
    (either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty,
    either__CDDL_Pulse_Types_slice·COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env29_type_1_pretty)
    =
        (w11,w20);
    let
    res3:
    ((evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty),
    (either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty,
    either__CDDL_Pulse_Types_slice·COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env29_type_1_pretty))
    =
        (w10,w21);
    let
    res10:
    ((evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty),
    (either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty,
    either__CDDL_Pulse_Types_slice·COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env29_type_1_pretty))
    =
        res3;
    let res20: evercddl_COSE_Sign_pretty = evercddl_COSE_Sign_pretty_right(res10);
    res20
}

/**
Serializer for evercddl_COSE_Sign
*/
pub fn
serialize_COSE_Sign(c: evercddl_COSE_Sign_pretty, out: &mut [u8]) ->
    usize
{
    let
    c·:
    ((evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty),
    (either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty,
    either__CDDL_Pulse_Types_slice·COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env29_type_1_pretty))
    =
        evercddl_COSE_Sign_pretty_left(c);
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let
    _letpattern:
    ((evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty),
    (either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty,
    either__CDDL_Pulse_Types_slice·COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env29_type_1_pretty))
    =
        c·;
    let res: bool =
        {
            let c1: (evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty) =
                _letpattern.0;
            let
            c2:
            (either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty,
            either__CDDL_Pulse_Types_slice·COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env29_type_1_pretty)
            =
                _letpattern.1;
            let
            _letpattern1: (evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty)
            =
                c1;
            let res1: bool =
                {
                    let c11: evercddl_empty_or_serialized_map_pretty = _letpattern1.0;
                    let c21: evercddl_header_map_pretty = _letpattern1.1;
                    let count: u64 = (&pcount)[0];
                    let res1: bool =
                        if count < 18446744073709551615u64
                        {
                            let size: usize = (&psize)[0];
                            let _letpattern2: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                            let _out0: &[u8] = _letpattern2.0;
                            let out1: &mut [u8] = _letpattern2.1;
                            let size1: usize = serialize_empty_or_serialized_map(c11, out1);
                            if size1 == 0usize
                            { false }
                            else
                            {
                                (&mut pcount)[0] = count.wrapping_add(1u64);
                                (&mut psize)[0] = size.wrapping_add(size1);
                                true
                            }
                        }
                        else
                        { false };
                    if res1
                    {
                        let count0: u64 = (&pcount)[0];
                        let res2: bool =
                            if count0 < 18446744073709551615u64
                            {
                                let size: usize = (&psize)[0];
                                let _letpattern2: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                                let _out0: &[u8] = _letpattern2.0;
                                let out1: &mut [u8] = _letpattern2.1;
                                let size1: usize = serialize_header_map(c21, out1);
                                if size1 == 0usize
                                { false }
                                else
                                {
                                    (&mut pcount)[0] = count0.wrapping_add(1u64);
                                    (&mut psize)[0] = size.wrapping_add(size1);
                                    true
                                }
                            }
                            else
                            { false };
                        res2
                    }
                    else
                    { false }
                };
            if res1
            {
                let
                _letpattern10:
                (either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty,
                either__CDDL_Pulse_Types_slice·COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env29_type_1_pretty)
                =
                    c2;
                let res2: bool =
                    {
                        let
                        c11:
                        either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
                        =
                            _letpattern10.0;
                        let
                        c21:
                        either__CDDL_Pulse_Types_slice·COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env29_type_1_pretty
                        =
                            _letpattern10.1;
                        let count: u64 = (&pcount)[0];
                        let res11: bool =
                            if count < 18446744073709551615u64
                            {
                                let size: usize = (&psize)[0];
                                let _letpattern2: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                                let _out0: &[u8] = _letpattern2.0;
                                let out1: &mut [u8] = _letpattern2.1;
                                let size1: usize =
                                    match c11
                                    {
                                        either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty::Inl
                                        { v: c12 }
                                        =>
                                          {
                                              let res: usize = serialize_bstr(c12, out1);
                                              res
                                          },
                                        either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty::Inr
                                        { v: c22 }
                                        =>
                                          {
                                              let res: usize = serialize_nil(c22, out1);
                                              res
                                          },
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                if size1 == 0usize
                                { false }
                                else
                                {
                                    (&mut pcount)[0] = count.wrapping_add(1u64);
                                    (&mut psize)[0] = size.wrapping_add(size1);
                                    true
                                }
                            }
                            else
                            { false };
                        if res11
                        {
                            let count0: u64 = (&pcount)[0];
                            let res2: bool =
                                if count0 < 18446744073709551615u64
                                {
                                    let size: usize = (&psize)[0];
                                    let _letpattern2: (&mut [u8], &mut [u8]) =
                                        out.split_at_mut(size);
                                    let _out0: &[u8] = _letpattern2.0;
                                    let out1: &mut [u8] = _letpattern2.1;
                                    let mut pcount1: [u64; 1] = [0u64; 1usize];
                                    let mut psize1: [usize; 1] = [0usize; 1usize];
                                    let res: bool =
                                        match c21
                                        {
                                            either__CDDL_Pulse_Types_slice·COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env29_type_1_pretty::Inl
                                            { v: c12 }
                                            =>
                                              {
                                                  let res: bool =
                                                      if c12.len() == 0usize
                                                      { false }
                                                      else
                                                      {
                                                          let mut pres: [bool; 1] = [true; 1usize];
                                                          let mut pi: [usize; 1] = [0usize; 1usize];
                                                          let slen: usize = c12.len();
                                                          let res: bool = (&pres)[0];
                                                          let mut cond: bool =
                                                              if res
                                                              {
                                                                  let i: usize = (&pi)[0];
                                                                  i < slen
                                                              }
                                                              else
                                                              { false };
                                                          while
                                                          cond
                                                          {
                                                              let i: usize = (&pi)[0];
                                                              let
                                                              x: evercddl_COSE_Signature_pretty
                                                              =
                                                                  c12[i];
                                                              let res0: bool =
                                                                  aux_env29_serialize_1(
                                                                      x,
                                                                      out1,
                                                                      &mut pcount1,
                                                                      &mut psize1
                                                                  );
                                                              if res0
                                                              {
                                                                  let i·: usize =
                                                                      i.wrapping_add(1usize);
                                                                  (&mut pi)[0] = i·
                                                              }
                                                              else
                                                              { (&mut pres)[0] = false };
                                                              let res2: bool = (&pres)[0];
                                                              let ite: bool =
                                                                  if res2
                                                                  {
                                                                      let i0: usize = (&pi)[0];
                                                                      i0 < slen
                                                                  }
                                                                  else
                                                                  { false };
                                                              cond = ite
                                                          };
                                                          (&pres)[0]
                                                      };
                                                  res
                                              },
                                            either__CDDL_Pulse_Types_slice·COSE_Format_aux_env29_type_1_pretty_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env29_type_1_pretty::Inr
                                            { v: c22 }
                                            =>
                                              {
                                                  let res: bool =
                                                      crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                          c22.cddl_array_iterator_contents
                                                      );
                                                  let em: bool = res;
                                                  let res0: bool =
                                                      if em
                                                      { false }
                                                      else
                                                      {
                                                          let
                                                          mut
                                                          pc:
                                                          [array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1_pretty;
                                                          1]
                                                          =
                                                              [c22; 1usize];
                                                          let mut pres: [bool; 1] = [true; 1usize];
                                                          let res0: bool = (&pres)[0];
                                                          let mut cond: bool =
                                                              if res0
                                                              {
                                                                  let
                                                                  c3:
                                                                  array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1_pretty
                                                                  =
                                                                      (&pc)[0];
                                                                  let res2: bool =
                                                                      crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                                          c3.cddl_array_iterator_contents
                                                                      );
                                                                  let em1: bool = res2;
                                                                  ! em1
                                                              }
                                                              else
                                                              { false };
                                                          while
                                                          cond
                                                          {
                                                              let
                                                              i:
                                                              array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1_pretty
                                                              =
                                                                  (&pc)[0];
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
                                                              let _test: bool =
                                                                  (i.cddl_array_iterator_impl_validate)(
                                                                      &mut pj
                                                                  );
                                                              crate::lowstar::ignore::ignore::<bool>(
                                                                  _test
                                                              );
                                                              let
                                                              ji:
                                                              crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                              =
                                                                  (&pj)[0];
                                                              let len1: u64 =
                                                                  crate::cbordetver::cbor_det_array_iterator_length(
                                                                      ji
                                                                  );
                                                              let
                                                              j:
                                                              array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1_pretty
                                                              =
                                                                  array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1_pretty
                                                                  {
                                                                      cddl_array_iterator_contents:
                                                                      ji,
                                                                      cddl_array_iterator_impl_validate:
                                                                      i.cddl_array_iterator_impl_validate,
                                                                      cddl_array_iterator_impl_parse:
                                                                      i.cddl_array_iterator_impl_parse
                                                                  };
                                                              (&mut pc)[0] = j;
                                                              let
                                                              tri:
                                                              crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                              =
                                                                  crate::cbordetver::cbor_det_array_iterator_truncate(
                                                                      i.cddl_array_iterator_contents,
                                                                      len0.wrapping_sub(len1)
                                                                  );
                                                              let
                                                              res2: evercddl_COSE_Signature_pretty
                                                              =
                                                                  (i.cddl_array_iterator_impl_parse)(
                                                                      tri
                                                                  );
                                                              let
                                                              x: evercddl_COSE_Signature_pretty
                                                              =
                                                                  res2;
                                                              let res3: bool =
                                                                  aux_env29_serialize_1(
                                                                      x,
                                                                      out1,
                                                                      &mut pcount1,
                                                                      &mut psize1
                                                                  );
                                                              if ! res3 { (&mut pres)[0] = false };
                                                              let res4: bool = (&pres)[0];
                                                              let ite: bool =
                                                                  if res4
                                                                  {
                                                                      let
                                                                      c3:
                                                                      array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1_pretty
                                                                      =
                                                                          (&pc)[0];
                                                                      let res20: bool =
                                                                          crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                                              c3.cddl_array_iterator_contents
                                                                          );
                                                                      let em1: bool = res20;
                                                                      ! em1
                                                                  }
                                                                  else
                                                                  { false };
                                                              cond = ite
                                                          };
                                                          (&pres)[0]
                                                      };
                                                  res0
                                              },
                                            _ => panic!("Incomplete pattern matching")
                                        };
                                    let _bind_c: usize =
                                        if res
                                        {
                                            let size1: usize = (&psize1)[0];
                                            let count1: u64 = (&pcount1)[0];
                                            crate::cbordetver::cbor_det_serialize_array(
                                                count1,
                                                out1,
                                                size1
                                            )
                                        }
                                        else
                                        { 0usize };
                                    let size1: usize = _bind_c;
                                    if size1 == 0usize
                                    { false }
                                    else
                                    {
                                        (&mut pcount)[0] = count0.wrapping_add(1u64);
                                        (&mut psize)[0] = size.wrapping_add(size1);
                                        true
                                    }
                                }
                                else
                                { false };
                            res2
                        }
                        else
                        { false }
                    };
                res2
            }
            else
            { false }
        };
    let _bind_c: usize =
        if res
        {
            let size: usize = (&psize)[0];
            let count: u64 = (&pcount)[0];
            crate::cbordetver::cbor_det_serialize_array(count, out, size)
        }
        else
        { 0usize };
    let res0: usize = _bind_c;
    res0
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_COSE_Sign_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_COSE_Sign_pretty <'a>, &'a [u8]) }
}

pub fn validate_and_parse_COSE_Sign <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_COSE_Sign_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_COSE_Sign_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_COSE_Sign(rl);
              if test
              {
                  let x: evercddl_COSE_Sign_pretty = parse_COSE_Sign(rl);
                  option__·COSE_Format_evercddl_COSE_Sign_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_COSE_Sign_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn is_empty_iterate_array_aux_env29_type_1(
    i:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1_pretty
) ->
    bool
{
    let res: bool =
        crate::cbordetver::cbor_det_array_iterator_is_empty(i.cddl_array_iterator_contents);
    res
}

pub fn next_iterate_array_aux_env29_type_1 <'a>(
    pi:
    &'a mut
    [array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1_pretty
    <'a>]
) ->
    evercddl_COSE_Signature_pretty
    <'a>
{
    let
    i:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1_pretty
    =
        pi[0];
    let len0: u64 =
        crate::cbordetver::cbor_det_array_iterator_length(i.cddl_array_iterator_contents);
    let mut pj: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [i.cddl_array_iterator_contents; 1usize];
    let _test: bool = (i.cddl_array_iterator_impl_validate)(&mut pj);
    crate::lowstar::ignore::ignore::<bool>(_test);
    let ji: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pj)[0];
    let len1: u64 = crate::cbordetver::cbor_det_array_iterator_length(ji);
    let
    j:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1_pretty
    =
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env29_type_1_pretty
        {
            cddl_array_iterator_contents: ji,
            cddl_array_iterator_impl_validate: i.cddl_array_iterator_impl_validate,
            cddl_array_iterator_impl_parse: i.cddl_array_iterator_impl_parse
        };
    pi[0] = j;
    let tri: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(
            i.cddl_array_iterator_contents,
            len0.wrapping_sub(len1)
        );
    let res: evercddl_COSE_Signature_pretty = (i.cddl_array_iterator_impl_parse)(tri);
    res
}

pub fn validate_COSE_Sign_Tagged(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let k: u8 = crate::cbordetver::cbor_det_major_type(c);
    if k == crate::cbordetveraux::cbor_major_type_tagged
    {
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let tag·: u64 =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 98u64 == tag·
        {
            let v10: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern0: crate::cbordetver::cbor_det_view = v10;
            let c·: crate::cbordetveraux::cbor_raw =
                match _letpattern0
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let res: bool = validate_COSE_Sign(c·);
            res
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_COSE_Sign_Tagged_pretty <'a> = evercddl_COSE_Sign_pretty <'a>;

pub fn uu___is_Mkevercddl_COSE_Sign_Tagged_pretty0(projectee: evercddl_COSE_Sign_pretty) ->
    bool
{
    crate::lowstar::ignore::ignore::<evercddl_COSE_Sign_pretty>(projectee);
    true
}

fn evercddl_COSE_Sign_Tagged_pretty_right <'a>(x1: evercddl_COSE_Sign_pretty <'a>) ->
    evercddl_COSE_Sign_pretty
    <'a>
{ x1 }

fn evercddl_COSE_Sign_Tagged_pretty_left <'a>(x3: evercddl_COSE_Sign_pretty <'a>) ->
    evercddl_COSE_Sign_pretty
    <'a>
{ x3 }

/**
Parser for evercddl_COSE_Sign_Tagged
*/
pub fn
parse_COSE_Sign_Tagged
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_COSE_Sign_pretty
    <'a>
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let cpl: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let res: evercddl_COSE_Sign_pretty = parse_COSE_Sign(cpl);
    let res1: evercddl_COSE_Sign_pretty = res;
    let res2: evercddl_COSE_Sign_pretty = evercddl_COSE_Sign_Tagged_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_COSE_Sign_Tagged
*/
pub fn
serialize_COSE_Sign_Tagged(c: evercddl_COSE_Sign_pretty, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_COSE_Sign_pretty = evercddl_COSE_Sign_Tagged_pretty_left(c);
    let c·1: (u64, evercddl_COSE_Sign_pretty) = (98u64,c·);
    let _letpattern: (u64, evercddl_COSE_Sign_pretty) = c·1;
    let res: usize =
        {
            let ctag: u64 = _letpattern.0;
            let cpayload: evercddl_COSE_Sign_pretty = _letpattern.1;
            let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
            if tsz == 0usize
            { 0usize }
            else
            {
                let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
                let out2: &mut [u8] = _letpattern1.1;
                let psz: usize = serialize_COSE_Sign(cpayload, out2);
                if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
            }
        };
    let res0: usize = res;
    res0
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_COSE_Sign_Tagged_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_COSE_Sign_pretty <'a>, &'a [u8]) }
}

pub fn validate_and_parse_COSE_Sign_Tagged <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_COSE_Sign_Tagged_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_COSE_Sign_Tagged_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_COSE_Sign_Tagged(rl);
              if test
              {
                  let x: evercddl_COSE_Sign_pretty = parse_COSE_Sign_Tagged(rl);
                  option__·COSE_Format_evercddl_COSE_Sign_Tagged_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_COSE_Sign_Tagged_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_COSE_Sign1(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let ty: u8 = crate::cbordetver::cbor_det_major_type(c);
    if ty == crate::cbordetveraux::cbor_major_type_array
    {
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Array { _0: a } =>
                  {
                      let
                      res: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                      =
                          crate::cbordetver::cbor_det_array_iterator_start(a);
                      res
                  },
                _ => panic!("Incomplete pattern matching")
            };
        let mut pi: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
            [i; 1usize];
        let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pi)[0];
        let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
        let test1: bool =
            if is_done
            { false }
            else
            {
                let c1: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                let test: bool = validate_empty_or_serialized_map(c1);
                test
            };
        let test10: bool =
            if test1
            {
                let i10: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0];
                let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i10);
                let test2: bool =
                    if is_done0
                    { false }
                    else
                    {
                        let c1: crate::cbordetveraux::cbor_raw =
                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                        let test: bool = validate_header_map(c1);
                        test
                    };
                test2
            }
            else
            { false };
        let b_success: bool =
            if test10
            {
                let i10: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0];
                let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i10);
                let test11: bool =
                    if is_done0
                    { false }
                    else
                    {
                        let c1: crate::cbordetveraux::cbor_raw =
                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                        let test: bool = validate_bstr(c1);
                        let test0: bool = if test { true } else { validate_nil(c1) };
                        test0
                    };
                let test2: bool =
                    if test11
                    {
                        let
                        i11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                        =
                            (&pi)[0];
                        let is_done1: bool =
                            crate::cbordetver::cbor_det_array_iterator_is_empty(i11);
                        let test2: bool =
                            if is_done1
                            { false }
                            else
                            {
                                let c1: crate::cbordetveraux::cbor_raw =
                                    crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                let test: bool = validate_bstr(c1);
                                test
                            };
                        test2
                    }
                    else
                    { false };
                test2
            }
            else
            { false };
        if b_success
        {
            let i·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pi)[0];
            let b_end: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i·);
            b_end
        }
        else
        { false }
    }
    else
    { false }
}

#[derive(PartialEq, Clone, Copy)]
pub struct evercddl_COSE_Sign1_pretty <'a>
{
    pub protected: evercddl_empty_or_serialized_map_pretty <'a>,
    pub unprotected: evercddl_header_map_pretty <'a>,
    pub payload: either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty <'a>,
    pub signature: &'a [u8]
}

pub fn uu___is_Mkevercddl_COSE_Sign1_pretty0(projectee: evercddl_COSE_Sign1_pretty) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_COSE_Sign1_pretty>(projectee);
    true
}

fn evercddl_COSE_Sign1_pretty_right <'a>(
    x4:
    ((evercddl_empty_or_serialized_map_pretty <'a>, evercddl_header_map_pretty <'a>),
    (either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty <'a>, &'a [u8]))
) ->
    evercddl_COSE_Sign1_pretty
    <'a>
{
    match x4
    {
        ((x5,x6),(x7,x8)) =>
          evercddl_COSE_Sign1_pretty { protected: x5, unprotected: x6, payload: x7, signature: x8 }
    }
}

fn evercddl_COSE_Sign1_pretty_left <'a>(x9: evercddl_COSE_Sign1_pretty <'a>) ->
    ((evercddl_empty_or_serialized_map_pretty <'a>, evercddl_header_map_pretty <'a>),
    (either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty <'a>, &'a [u8]))
{
    let x15: evercddl_empty_or_serialized_map_pretty = x9.protected;
    let x16: evercddl_header_map_pretty = x9.unprotected;
    let x17: either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty = x9.payload;
    let x18: &[u8] = x9.signature;
    ((x15,x16),(x17,x18))
}

/**
Parser for evercddl_COSE_Sign1
*/
pub fn
parse_COSE_Sign1
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_COSE_Sign1_pretty
    <'a>
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let ar: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Array { _0: a } =>
              {
                  let res: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                      crate::cbordetver::cbor_det_array_iterator_start(a);
                  res
              },
            _ => panic!("Incomplete pattern matching")
        };
    let rlen0: u64 = crate::cbordetver::cbor_det_array_iterator_length(ar);
    let mut pc: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [ar; 1usize];
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0];
    let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i);
    let test1: bool =
        if is_done
        { false }
        else
        {
            let c1: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
            let test: bool = validate_empty_or_serialized_map(c1);
            test
        };
    let _tmp: bool =
        if test1
        {
            let i0: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc)[0];
            let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i0);
            let test2: bool =
                if is_done0
                { false }
                else
                {
                    let c1: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
                    let test: bool = validate_header_map(c1);
                    test
                };
            test2
        }
        else
        { false };
    crate::lowstar::ignore::ignore::<bool>(_tmp);
    let c1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0];
    let rlen1: u64 = crate::cbordetver::cbor_det_array_iterator_length(c1);
    let c0·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(ar, rlen0.wrapping_sub(rlen1));
    let rlen01: u64 = crate::cbordetver::cbor_det_array_iterator_length(c0·);
    let mut pc1: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·; 1usize];
    let i0: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc1)[0];
    let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i0);
    let _tmp1: bool =
        if is_done0
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc1);
            let test: bool = validate_empty_or_serialized_map(c2);
            test
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp1);
    let c11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc1)[0];
    let rlen11: u64 = crate::cbordetver::cbor_det_array_iterator_length(c11);
    let c0·1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c0·, rlen01.wrapping_sub(rlen11));
    let mut pc2: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·1; 1usize];
    let x: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc2);
    let res: evercddl_empty_or_serialized_map_pretty = parse_empty_or_serialized_map(x);
    let w1: evercddl_empty_or_serialized_map_pretty = res;
    let mut pc20: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c11; 1usize];
    let x0: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc20);
    let res0: evercddl_header_map_pretty = parse_header_map(x0);
    let w2: evercddl_header_map_pretty = res0;
    let w10: (evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty) = (w1,w2);
    let rlen010: u64 = crate::cbordetver::cbor_det_array_iterator_length(c1);
    let mut pc10: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c1; 1usize];
    let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc10)[0];
    let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
    let _tmp10: bool =
        if is_done1
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc10);
            let test: bool = validate_bstr(c2);
            let test0: bool = if test { true } else { validate_nil(c2) };
            test0
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp10);
    let c110: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc10)[0];
    let rlen110: u64 = crate::cbordetver::cbor_det_array_iterator_length(c110);
    let c0·10: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c1, rlen010.wrapping_sub(rlen110));
    let mut pc21: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·10; 1usize];
    let x1: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc21);
    let test: bool = validate_bstr(x1);
    let res1: either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty =
        if test
        {
            let res1: &[u8] = parse_bstr(x1);
            either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty::Inl
            { v: res1 }
        }
        else
        {
            let res1: evercddl_nil_pretty = parse_nil(x1);
            either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty::Inr
            { v: res1 }
        };
    let w11: either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty = res1;
    let mut pc22: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c110; 1usize];
    let x2: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc22);
    let res2: &[u8] = parse_bstr(x2);
    let w20: &[u8] = res2;
    let w21: (either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty, &[u8]) =
        (w11,w20);
    let
    res3:
    ((evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty),
    (either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty, &[u8]))
    =
        (w10,w21);
    let
    res10:
    ((evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty),
    (either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty, &[u8]))
    =
        res3;
    let res20: evercddl_COSE_Sign1_pretty = evercddl_COSE_Sign1_pretty_right(res10);
    res20
}

/**
Serializer for evercddl_COSE_Sign1
*/
pub fn
serialize_COSE_Sign1(c: evercddl_COSE_Sign1_pretty, out: &mut [u8]) ->
    usize
{
    let
    c·:
    ((evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty),
    (either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty, &[u8]))
    =
        evercddl_COSE_Sign1_pretty_left(c);
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let
    _letpattern:
    ((evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty),
    (either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty, &[u8]))
    =
        c·;
    let res: bool =
        {
            let c1: (evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty) =
                _letpattern.0;
            let
            c2: (either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty, &[u8])
            =
                _letpattern.1;
            let
            _letpattern1: (evercddl_empty_or_serialized_map_pretty, evercddl_header_map_pretty)
            =
                c1;
            let res1: bool =
                {
                    let c11: evercddl_empty_or_serialized_map_pretty = _letpattern1.0;
                    let c21: evercddl_header_map_pretty = _letpattern1.1;
                    let count: u64 = (&pcount)[0];
                    let res1: bool =
                        if count < 18446744073709551615u64
                        {
                            let size: usize = (&psize)[0];
                            let _letpattern2: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                            let _out0: &[u8] = _letpattern2.0;
                            let out1: &mut [u8] = _letpattern2.1;
                            let size1: usize = serialize_empty_or_serialized_map(c11, out1);
                            if size1 == 0usize
                            { false }
                            else
                            {
                                (&mut pcount)[0] = count.wrapping_add(1u64);
                                (&mut psize)[0] = size.wrapping_add(size1);
                                true
                            }
                        }
                        else
                        { false };
                    if res1
                    {
                        let count0: u64 = (&pcount)[0];
                        let res2: bool =
                            if count0 < 18446744073709551615u64
                            {
                                let size: usize = (&psize)[0];
                                let _letpattern2: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                                let _out0: &[u8] = _letpattern2.0;
                                let out1: &mut [u8] = _letpattern2.1;
                                let size1: usize = serialize_header_map(c21, out1);
                                if size1 == 0usize
                                { false }
                                else
                                {
                                    (&mut pcount)[0] = count0.wrapping_add(1u64);
                                    (&mut psize)[0] = size.wrapping_add(size1);
                                    true
                                }
                            }
                            else
                            { false };
                        res2
                    }
                    else
                    { false }
                };
            if res1
            {
                let
                _letpattern10:
                (either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty, &[u8])
                =
                    c2;
                let res2: bool =
                    {
                        let
                        c11:
                        either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
                        =
                            _letpattern10.0;
                        let c21: &[u8] = _letpattern10.1;
                        let count: u64 = (&pcount)[0];
                        let res11: bool =
                            if count < 18446744073709551615u64
                            {
                                let size: usize = (&psize)[0];
                                let _letpattern2: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                                let _out0: &[u8] = _letpattern2.0;
                                let out1: &mut [u8] = _letpattern2.1;
                                let size1: usize =
                                    match c11
                                    {
                                        either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty::Inl
                                        { v: c12 }
                                        =>
                                          {
                                              let res: usize = serialize_bstr(c12, out1);
                                              res
                                          },
                                        either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty::Inr
                                        { v: c22 }
                                        =>
                                          {
                                              let res: usize = serialize_nil(c22, out1);
                                              res
                                          },
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                if size1 == 0usize
                                { false }
                                else
                                {
                                    (&mut pcount)[0] = count.wrapping_add(1u64);
                                    (&mut psize)[0] = size.wrapping_add(size1);
                                    true
                                }
                            }
                            else
                            { false };
                        if res11
                        {
                            let count0: u64 = (&pcount)[0];
                            let res2: bool =
                                if count0 < 18446744073709551615u64
                                {
                                    let size: usize = (&psize)[0];
                                    let _letpattern2: (&mut [u8], &mut [u8]) =
                                        out.split_at_mut(size);
                                    let _out0: &[u8] = _letpattern2.0;
                                    let out1: &mut [u8] = _letpattern2.1;
                                    let size1: usize = serialize_bstr(c21, out1);
                                    if size1 == 0usize
                                    { false }
                                    else
                                    {
                                        (&mut pcount)[0] = count0.wrapping_add(1u64);
                                        (&mut psize)[0] = size.wrapping_add(size1);
                                        true
                                    }
                                }
                                else
                                { false };
                            res2
                        }
                        else
                        { false }
                    };
                res2
            }
            else
            { false }
        };
    let _bind_c: usize =
        if res
        {
            let size: usize = (&psize)[0];
            let count: u64 = (&pcount)[0];
            crate::cbordetver::cbor_det_serialize_array(count, out, size)
        }
        else
        { 0usize };
    let res0: usize = _bind_c;
    res0
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_COSE_Sign1_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_COSE_Sign1_pretty <'a>, &'a [u8]) }
}

pub fn validate_and_parse_COSE_Sign1 <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_COSE_Sign1_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_COSE_Sign1_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_COSE_Sign1(rl);
              if test
              {
                  let x: evercddl_COSE_Sign1_pretty = parse_COSE_Sign1(rl);
                  option__·COSE_Format_evercddl_COSE_Sign1_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_COSE_Sign1_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_COSE_Untagged_Message(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let test: bool = validate_COSE_Sign(c);
    if test { true } else { validate_COSE_Sign1(c) }
}

#[derive(PartialEq, Clone, Copy)]
enum evercddl_COSE_Untagged_Message <'a>
{
    Inl { v: evercddl_COSE_Sign_pretty <'a> },
    Inr { v: evercddl_COSE_Sign1_pretty <'a> }
}

#[derive(PartialEq, Clone, Copy)]
enum evercddl_COSE_Untagged_Message_pretty_tags
{
    Mkevercddl_COSE_Untagged_Message_pretty0,
    Mkevercddl_COSE_Untagged_Message_pretty1
}

#[derive(PartialEq, Clone, Copy)]
pub enum evercddl_COSE_Untagged_Message_pretty <'a>
{
    Mkevercddl_COSE_Untagged_Message_pretty0 { _x0: evercddl_COSE_Sign_pretty <'a> },
    Mkevercddl_COSE_Untagged_Message_pretty1 { _x0: evercddl_COSE_Sign1_pretty <'a> }
}

pub fn uu___is_Mkevercddl_COSE_Untagged_Message_pretty0(
    projectee: evercddl_COSE_Untagged_Message_pretty
) ->
    bool
{
    match projectee
    {
        evercddl_COSE_Untagged_Message_pretty::Mkevercddl_COSE_Untagged_Message_pretty0 { .. } =>
          true,
        _ => false
    }
}

pub fn uu___is_Mkevercddl_COSE_Untagged_Message_pretty1(
    projectee: evercddl_COSE_Untagged_Message_pretty
) ->
    bool
{
    match projectee
    {
        evercddl_COSE_Untagged_Message_pretty::Mkevercddl_COSE_Untagged_Message_pretty1 { .. } =>
          true,
        _ => false
    }
}

fn evercddl_COSE_Untagged_Message_pretty_right <'a>(x2: evercddl_COSE_Untagged_Message <'a>) ->
    evercddl_COSE_Untagged_Message_pretty
    <'a>
{
    match x2
    {
        evercddl_COSE_Untagged_Message::Inl { v: x3 } =>
          evercddl_COSE_Untagged_Message_pretty::Mkevercddl_COSE_Untagged_Message_pretty0
          { _x0: x3 },
        evercddl_COSE_Untagged_Message::Inr { v: x4 } =>
          evercddl_COSE_Untagged_Message_pretty::Mkevercddl_COSE_Untagged_Message_pretty1
          { _x0: x4 },
        _ => panic!("Incomplete pattern matching")
    }
}

fn evercddl_COSE_Untagged_Message_pretty_left <'a>(
    x7: evercddl_COSE_Untagged_Message_pretty <'a>
) ->
    evercddl_COSE_Untagged_Message
    <'a>
{
    match x7
    {
        evercddl_COSE_Untagged_Message_pretty::Mkevercddl_COSE_Untagged_Message_pretty0
        { _x0: x10 }
        => evercddl_COSE_Untagged_Message::Inl { v: x10 },
        evercddl_COSE_Untagged_Message_pretty::Mkevercddl_COSE_Untagged_Message_pretty1
        { _x0: x12 }
        => evercddl_COSE_Untagged_Message::Inr { v: x12 },
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Parser for evercddl_COSE_Untagged_Message
*/
pub fn
parse_COSE_Untagged_Message
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_COSE_Untagged_Message_pretty
    <'a>
{
    let test: bool = validate_COSE_Sign(c);
    let res1: evercddl_COSE_Untagged_Message =
        if test
        {
            let res: evercddl_COSE_Sign_pretty = parse_COSE_Sign(c);
            evercddl_COSE_Untagged_Message::Inl { v: res }
        }
        else
        {
            let res: evercddl_COSE_Sign1_pretty = parse_COSE_Sign1(c);
            evercddl_COSE_Untagged_Message::Inr { v: res }
        };
    let res2: evercddl_COSE_Untagged_Message_pretty =
        evercddl_COSE_Untagged_Message_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_COSE_Untagged_Message
*/
pub fn
serialize_COSE_Untagged_Message(c: evercddl_COSE_Untagged_Message_pretty, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_COSE_Untagged_Message = evercddl_COSE_Untagged_Message_pretty_left(c);
    match c·
    {
        evercddl_COSE_Untagged_Message::Inl { v: c1 } =>
          {
              let res: usize = serialize_COSE_Sign(c1, out);
              res
          },
        evercddl_COSE_Untagged_Message::Inr { v: c2 } =>
          {
              let res: usize = serialize_COSE_Sign1(c2, out);
              res
          },
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_COSE_Untagged_Message_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_COSE_Untagged_Message_pretty <'a>, &'a [u8]) }
}

pub fn validate_and_parse_COSE_Untagged_Message <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_COSE_Untagged_Message_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_COSE_Untagged_Message_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_COSE_Untagged_Message(rl);
              if test
              {
                  let x: evercddl_COSE_Untagged_Message_pretty = parse_COSE_Untagged_Message(rl);
                  option__·COSE_Format_evercddl_COSE_Untagged_Message_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_COSE_Untagged_Message_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_COSE_Sign1_Tagged(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let k: u8 = crate::cbordetver::cbor_det_major_type(c);
    if k == crate::cbordetveraux::cbor_major_type_tagged
    {
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let tag·: u64 =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 18u64 == tag·
        {
            let v10: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern0: crate::cbordetver::cbor_det_view = v10;
            let c·: crate::cbordetveraux::cbor_raw =
                match _letpattern0
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let res: bool = validate_COSE_Sign1(c·);
            res
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_COSE_Sign1_Tagged_pretty <'a> = evercddl_COSE_Sign1_pretty <'a>;

pub fn uu___is_Mkevercddl_COSE_Sign1_Tagged_pretty0(projectee: evercddl_COSE_Sign1_pretty) ->
    bool
{
    crate::lowstar::ignore::ignore::<evercddl_COSE_Sign1_pretty>(projectee);
    true
}

fn evercddl_COSE_Sign1_Tagged_pretty_right <'a>(x1: evercddl_COSE_Sign1_pretty <'a>) ->
    evercddl_COSE_Sign1_pretty
    <'a>
{ x1 }

fn evercddl_COSE_Sign1_Tagged_pretty_left <'a>(x3: evercddl_COSE_Sign1_pretty <'a>) ->
    evercddl_COSE_Sign1_pretty
    <'a>
{ x3 }

/**
Parser for evercddl_COSE_Sign1_Tagged
*/
pub fn
parse_COSE_Sign1_Tagged
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_COSE_Sign1_pretty
    <'a>
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let cpl: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let res: evercddl_COSE_Sign1_pretty = parse_COSE_Sign1(cpl);
    let res1: evercddl_COSE_Sign1_pretty = res;
    let res2: evercddl_COSE_Sign1_pretty = evercddl_COSE_Sign1_Tagged_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_COSE_Sign1_Tagged
*/
pub fn
serialize_COSE_Sign1_Tagged(c: evercddl_COSE_Sign1_pretty, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_COSE_Sign1_pretty = evercddl_COSE_Sign1_Tagged_pretty_left(c);
    let c·1: (u64, evercddl_COSE_Sign1_pretty) = (18u64,c·);
    let _letpattern: (u64, evercddl_COSE_Sign1_pretty) = c·1;
    let res: usize =
        {
            let ctag: u64 = _letpattern.0;
            let cpayload: evercddl_COSE_Sign1_pretty = _letpattern.1;
            let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
            if tsz == 0usize
            { 0usize }
            else
            {
                let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
                let out2: &mut [u8] = _letpattern1.1;
                let psz: usize = serialize_COSE_Sign1(cpayload, out2);
                if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
            }
        };
    let res0: usize = res;
    res0
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_COSE_Sign1_Tagged_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_COSE_Sign1_pretty <'a>, &'a [u8]) }
}

pub fn validate_and_parse_COSE_Sign1_Tagged <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_COSE_Sign1_Tagged_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_COSE_Sign1_Tagged_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_COSE_Sign1_Tagged(rl);
              if test
              {
                  let x: evercddl_COSE_Sign1_pretty = parse_COSE_Sign1_Tagged(rl);
                  option__·COSE_Format_evercddl_COSE_Sign1_Tagged_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_COSE_Sign1_Tagged_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_COSE_Tagged_Message(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let test: bool = validate_COSE_Sign_Tagged(c);
    if test { true } else { validate_COSE_Sign1_Tagged(c) }
}

#[derive(PartialEq, Clone, Copy)]
enum evercddl_COSE_Tagged_Message <'a>
{
    Inl { v: evercddl_COSE_Sign_pretty <'a> },
    Inr { v: evercddl_COSE_Sign1_pretty <'a> }
}

#[derive(PartialEq, Clone, Copy)]
enum evercddl_COSE_Tagged_Message_pretty_tags
{
    Mkevercddl_COSE_Tagged_Message_pretty0,
    Mkevercddl_COSE_Tagged_Message_pretty1
}

#[derive(PartialEq, Clone, Copy)]
pub enum evercddl_COSE_Tagged_Message_pretty <'a>
{
    Mkevercddl_COSE_Tagged_Message_pretty0 { _x0: evercddl_COSE_Sign_pretty <'a> },
    Mkevercddl_COSE_Tagged_Message_pretty1 { _x0: evercddl_COSE_Sign1_pretty <'a> }
}

pub fn uu___is_Mkevercddl_COSE_Tagged_Message_pretty0(
    projectee: evercddl_COSE_Tagged_Message_pretty
) ->
    bool
{
    match projectee
    {
        evercddl_COSE_Tagged_Message_pretty::Mkevercddl_COSE_Tagged_Message_pretty0 { .. } => true,
        _ => false
    }
}

pub fn uu___is_Mkevercddl_COSE_Tagged_Message_pretty1(
    projectee: evercddl_COSE_Tagged_Message_pretty
) ->
    bool
{
    match projectee
    {
        evercddl_COSE_Tagged_Message_pretty::Mkevercddl_COSE_Tagged_Message_pretty1 { .. } => true,
        _ => false
    }
}

fn evercddl_COSE_Tagged_Message_pretty_right <'a>(x2: evercddl_COSE_Tagged_Message <'a>) ->
    evercddl_COSE_Tagged_Message_pretty
    <'a>
{
    match x2
    {
        evercddl_COSE_Tagged_Message::Inl { v: x3 } =>
          evercddl_COSE_Tagged_Message_pretty::Mkevercddl_COSE_Tagged_Message_pretty0 { _x0: x3 },
        evercddl_COSE_Tagged_Message::Inr { v: x4 } =>
          evercddl_COSE_Tagged_Message_pretty::Mkevercddl_COSE_Tagged_Message_pretty1 { _x0: x4 },
        _ => panic!("Incomplete pattern matching")
    }
}

fn evercddl_COSE_Tagged_Message_pretty_left <'a>(x7: evercddl_COSE_Tagged_Message_pretty <'a>) ->
    evercddl_COSE_Tagged_Message
    <'a>
{
    match x7
    {
        evercddl_COSE_Tagged_Message_pretty::Mkevercddl_COSE_Tagged_Message_pretty0 { _x0: x10 } =>
          evercddl_COSE_Tagged_Message::Inl { v: x10 },
        evercddl_COSE_Tagged_Message_pretty::Mkevercddl_COSE_Tagged_Message_pretty1 { _x0: x12 } =>
          evercddl_COSE_Tagged_Message::Inr { v: x12 },
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Parser for evercddl_COSE_Tagged_Message
*/
pub fn
parse_COSE_Tagged_Message
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_COSE_Tagged_Message_pretty
    <'a>
{
    let test: bool = validate_COSE_Sign_Tagged(c);
    let res1: evercddl_COSE_Tagged_Message =
        if test
        {
            let res: evercddl_COSE_Sign_pretty = parse_COSE_Sign_Tagged(c);
            evercddl_COSE_Tagged_Message::Inl { v: res }
        }
        else
        {
            let res: evercddl_COSE_Sign1_pretty = parse_COSE_Sign1_Tagged(c);
            evercddl_COSE_Tagged_Message::Inr { v: res }
        };
    let res2: evercddl_COSE_Tagged_Message_pretty =
        evercddl_COSE_Tagged_Message_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_COSE_Tagged_Message
*/
pub fn
serialize_COSE_Tagged_Message(c: evercddl_COSE_Tagged_Message_pretty, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_COSE_Tagged_Message = evercddl_COSE_Tagged_Message_pretty_left(c);
    match c·
    {
        evercddl_COSE_Tagged_Message::Inl { v: c1 } =>
          {
              let res: usize = serialize_COSE_Sign_Tagged(c1, out);
              res
          },
        evercddl_COSE_Tagged_Message::Inr { v: c2 } =>
          {
              let res: usize = serialize_COSE_Sign1_Tagged(c2, out);
              res
          },
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_COSE_Tagged_Message_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_COSE_Tagged_Message_pretty <'a>, &'a [u8]) }
}

pub fn validate_and_parse_COSE_Tagged_Message <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_COSE_Tagged_Message_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_COSE_Tagged_Message_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_COSE_Tagged_Message(rl);
              if test
              {
                  let x: evercddl_COSE_Tagged_Message_pretty = parse_COSE_Tagged_Message(rl);
                  option__·COSE_Format_evercddl_COSE_Tagged_Message_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_COSE_Tagged_Message_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_COSE_Messages(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let test: bool = validate_COSE_Untagged_Message(c);
    if test { true } else { validate_COSE_Tagged_Message(c) }
}

#[derive(PartialEq, Clone, Copy)]
enum evercddl_COSE_Messages <'a>
{
    Inl { v: evercddl_COSE_Untagged_Message_pretty <'a> },
    Inr { v: evercddl_COSE_Tagged_Message_pretty <'a> }
}

#[derive(PartialEq, Clone, Copy)]
enum evercddl_COSE_Messages_pretty_tags
{
    Mkevercddl_COSE_Messages_pretty0,
    Mkevercddl_COSE_Messages_pretty1
}

#[derive(PartialEq, Clone, Copy)]
pub enum evercddl_COSE_Messages_pretty <'a>
{
    Mkevercddl_COSE_Messages_pretty0 { _x0: evercddl_COSE_Untagged_Message_pretty <'a> },
    Mkevercddl_COSE_Messages_pretty1 { _x0: evercddl_COSE_Tagged_Message_pretty <'a> }
}

pub fn uu___is_Mkevercddl_COSE_Messages_pretty0(projectee: evercddl_COSE_Messages_pretty) ->
    bool
{
    match projectee
    { evercddl_COSE_Messages_pretty::Mkevercddl_COSE_Messages_pretty0 { .. } => true, _ => false }
}

pub fn uu___is_Mkevercddl_COSE_Messages_pretty1(projectee: evercddl_COSE_Messages_pretty) ->
    bool
{
    match projectee
    { evercddl_COSE_Messages_pretty::Mkevercddl_COSE_Messages_pretty1 { .. } => true, _ => false }
}

fn evercddl_COSE_Messages_pretty_right <'a>(x2: evercddl_COSE_Messages <'a>) ->
    evercddl_COSE_Messages_pretty
    <'a>
{
    match x2
    {
        evercddl_COSE_Messages::Inl { v: x3 } =>
          evercddl_COSE_Messages_pretty::Mkevercddl_COSE_Messages_pretty0 { _x0: x3 },
        evercddl_COSE_Messages::Inr { v: x4 } =>
          evercddl_COSE_Messages_pretty::Mkevercddl_COSE_Messages_pretty1 { _x0: x4 },
        _ => panic!("Incomplete pattern matching")
    }
}

fn evercddl_COSE_Messages_pretty_left <'a>(x7: evercddl_COSE_Messages_pretty <'a>) ->
    evercddl_COSE_Messages
    <'a>
{
    match x7
    {
        evercddl_COSE_Messages_pretty::Mkevercddl_COSE_Messages_pretty0 { _x0: x10 } =>
          evercddl_COSE_Messages::Inl { v: x10 },
        evercddl_COSE_Messages_pretty::Mkevercddl_COSE_Messages_pretty1 { _x0: x12 } =>
          evercddl_COSE_Messages::Inr { v: x12 },
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Parser for evercddl_COSE_Messages
*/
pub fn
parse_COSE_Messages
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_COSE_Messages_pretty
    <'a>
{
    let test: bool = validate_COSE_Untagged_Message(c);
    let res1: evercddl_COSE_Messages =
        if test
        {
            let res: evercddl_COSE_Untagged_Message_pretty = parse_COSE_Untagged_Message(c);
            evercddl_COSE_Messages::Inl { v: res }
        }
        else
        {
            let res: evercddl_COSE_Tagged_Message_pretty = parse_COSE_Tagged_Message(c);
            evercddl_COSE_Messages::Inr { v: res }
        };
    let res2: evercddl_COSE_Messages_pretty = evercddl_COSE_Messages_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_COSE_Messages
*/
pub fn
serialize_COSE_Messages(c: evercddl_COSE_Messages_pretty, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_COSE_Messages = evercddl_COSE_Messages_pretty_left(c);
    match c·
    {
        evercddl_COSE_Messages::Inl { v: c1 } =>
          {
              let res: usize = serialize_COSE_Untagged_Message(c1, out);
              res
          },
        evercddl_COSE_Messages::Inr { v: c2 } =>
          {
              let res: usize = serialize_COSE_Tagged_Message(c2, out);
              res
          },
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_COSE_Messages_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_COSE_Messages_pretty <'a>, &'a [u8]) }
}

pub fn validate_and_parse_COSE_Messages <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_COSE_Messages_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_COSE_Messages_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_COSE_Messages(rl);
              if test
              {
                  let x: evercddl_COSE_Messages_pretty = parse_COSE_Messages(rl);
                  option__·COSE_Format_evercddl_COSE_Messages_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_COSE_Messages_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_Sig_structure(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let ty: u8 = crate::cbordetver::cbor_det_major_type(c);
    if ty == crate::cbordetveraux::cbor_major_type_array
    {
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Array { _0: a } =>
                  {
                      let
                      res: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                      =
                          crate::cbordetver::cbor_det_array_iterator_start(a);
                      res
                  },
                _ => panic!("Incomplete pattern matching")
            };
        let mut pi: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
            [i; 1usize];
        let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pi)[0];
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
                let test0: bool =
                    if test
                    {
                        let v10: crate::cbordetver::cbor_det_view =
                            crate::cbordetver::cbor_det_destruct(c1);
                        let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                        let s: &[u8] =
                            match _letpattern0
                            {
                                crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                                _ => panic!("Incomplete pattern matching")
                            };
                        if s.len() != 9u64 as usize
                        { false }
                        else
                        {
                            let x: u8 = s[0usize];
                            let i·: usize = 1usize;
                            let res: bool =
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
                                                            let i·7: usize =
                                                                i·6.wrapping_add(1usize);
                                                            if x7 == 114u8
                                                            {
                                                                let x8: u8 = s[i·7];
                                                                if x8 == 101u8
                                                                { true }
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
                                { false };
                            res
                        }
                    }
                    else
                    { false };
                let test1: bool =
                    if test0
                    { true }
                    else
                    {
                        let mt0: u8 = crate::cbordetver::cbor_det_major_type(c1);
                        let test1: bool = mt0 == crate::cbordetveraux::cbor_major_type_text_string;
                        if test1
                        {
                            let v10: crate::cbordetver::cbor_det_view =
                                crate::cbordetver::cbor_det_destruct(c1);
                            let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                            let s: &[u8] =
                                match _letpattern0
                                {
                                    crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                                    _ => panic!("Incomplete pattern matching")
                                };
                            if s.len() != 10u64 as usize
                            { false }
                            else
                            {
                                let x: u8 = s[0usize];
                                let i·: usize = 1usize;
                                let res: bool =
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
                                                            let i·6: usize =
                                                                i·5.wrapping_add(1usize);
                                                            if x6 == 117u8
                                                            {
                                                                let x7: u8 = s[i·6];
                                                                let i·7: usize =
                                                                    i·6.wrapping_add(1usize);
                                                                if x7 == 114u8
                                                                {
                                                                    let x8: u8 = s[i·7];
                                                                    let i·8: usize =
                                                                        i·7.wrapping_add(1usize);
                                                                    if x8 == 101u8
                                                                    {
                                                                        let x9: u8 = s[i·8];
                                                                        if x9 == 49u8
                                                                        { true }
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
                                    else
                                    { false };
                                res
                            }
                        }
                        else
                        { false }
                    };
                test1
            };
        let b_success: bool =
            if test1
            {
                let i10: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0];
                let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i10);
                let test11: bool =
                    if is_done0
                    { false }
                    else
                    {
                        let c1: crate::cbordetveraux::cbor_raw =
                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                        let test: bool = validate_empty_or_serialized_map(c1);
                        test
                    };
                let test2: bool =
                    if test11
                    {
                        let
                        i11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                        =
                            (&pi)[0];
                        let
                        i2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                        =
                            (&pi)[0];
                        let is_done1: bool =
                            crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
                        let test12: bool =
                            if is_done1
                            { false }
                            else
                            {
                                let c1: crate::cbordetveraux::cbor_raw =
                                    crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                let test: bool = validate_empty_or_serialized_map(c1);
                                test
                            };
                        let test120: bool =
                            if test12
                            {
                                let
                                i20:
                                crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                =
                                    (&pi)[0];
                                let is_done2: bool =
                                    crate::cbordetver::cbor_det_array_iterator_is_empty(i20);
                                let test13: bool =
                                    if is_done2
                                    { false }
                                    else
                                    {
                                        let c1: crate::cbordetveraux::cbor_raw =
                                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                        let test: bool = validate_bstr(c1);
                                        test
                                    };
                                let test2: bool =
                                    if test13
                                    {
                                        let
                                        i21:
                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                        =
                                            (&pi)[0];
                                        let is_done3: bool =
                                            crate::cbordetver::cbor_det_array_iterator_is_empty(i21);
                                        let test2: bool =
                                            if is_done3
                                            { false }
                                            else
                                            {
                                                let c1: crate::cbordetveraux::cbor_raw =
                                                    crate::cbordetver::cbor_det_array_iterator_next(
                                                        &mut pi
                                                    );
                                                let test: bool = validate_bstr(c1);
                                                test
                                            };
                                        test2
                                    }
                                    else
                                    { false };
                                test2
                            }
                            else
                            { false };
                        let test2: bool =
                            if test120
                            { true }
                            else
                            {
                                (&mut pi)[0] = i11;
                                let
                                i20:
                                crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                =
                                    (&pi)[0];
                                let is_done2: bool =
                                    crate::cbordetver::cbor_det_array_iterator_is_empty(i20);
                                let test13: bool =
                                    if is_done2
                                    { false }
                                    else
                                    {
                                        let c1: crate::cbordetveraux::cbor_raw =
                                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                        let test: bool = validate_bstr(c1);
                                        test
                                    };
                                let res: bool =
                                    if test13
                                    {
                                        let
                                        i21:
                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                        =
                                            (&pi)[0];
                                        let is_done3: bool =
                                            crate::cbordetver::cbor_det_array_iterator_is_empty(i21);
                                        let test2: bool =
                                            if is_done3
                                            { false }
                                            else
                                            {
                                                let c1: crate::cbordetveraux::cbor_raw =
                                                    crate::cbordetver::cbor_det_array_iterator_next(
                                                        &mut pi
                                                    );
                                                let test: bool = validate_bstr(c1);
                                                test
                                            };
                                        test2
                                    }
                                    else
                                    { false };
                                res
                            };
                        test2
                    }
                    else
                    { false };
                test2
            }
            else
            { false };
        if b_success
        {
            let i·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pi)[0];
            let b_end: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i·);
            b_end
        }
        else
        { false }
    }
    else
    { false }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·
<'a>
{
    Inl { v: (evercddl_empty_or_serialized_map_pretty <'a>, (&'a [u8], &'a [u8])) },
    Inr { v: (&'a [u8], &'a [u8]) }
}

#[derive(PartialEq, Clone, Copy)]
pub struct evercddl_Sig_structure_pretty <'a>
{
    pub context: evercddl_int_tags,
    pub body_protected: evercddl_empty_or_serialized_map_pretty <'a>,
    pub _x0:
    either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·
    <'a>
}

pub fn uu___is_Mkevercddl_Sig_structure_pretty0(projectee: evercddl_Sig_structure_pretty) ->
    bool
{
    crate::lowstar::ignore::ignore::<evercddl_Sig_structure_pretty>(projectee);
    true
}

fn evercddl_Sig_structure_pretty_right <'a>(
    x3:
    (evercddl_int_tags,
    (evercddl_empty_or_serialized_map_pretty
    <'a>,
    either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·
    <'a>))
) ->
    evercddl_Sig_structure_pretty
    <'a>
{
    match x3
    { (x4,(x5,x6)) => evercddl_Sig_structure_pretty { context: x4, body_protected: x5, _x0: x6 } }
}

fn evercddl_Sig_structure_pretty_left <'a>(x7: evercddl_Sig_structure_pretty <'a>) ->
    (evercddl_int_tags,
    (evercddl_empty_or_serialized_map_pretty
    <'a>,
    either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·
    <'a>))
{
    let x12: evercddl_int_tags = x7.context;
    let x13: evercddl_empty_or_serialized_map_pretty = x7.body_protected;
    let
    x14:
    either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·
    =
        x7._x0;
    (x12,(x13,x14))
}

/**
Parser for evercddl_Sig_structure
*/
pub fn
parse_Sig_structure
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_Sig_structure_pretty
    <'a>
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let ar: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Array { _0: a } =>
              {
                  let res: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                      crate::cbordetver::cbor_det_array_iterator_start(a);
                  res
              },
            _ => panic!("Incomplete pattern matching")
        };
    let rlen0: u64 = crate::cbordetver::cbor_det_array_iterator_length(ar);
    let mut pc: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [ar; 1usize];
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0];
    let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i);
    let _tmp: bool =
        if is_done
        { false }
        else
        {
            let c1: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
            let test: bool = mt == crate::cbordetveraux::cbor_major_type_text_string;
            let test0: bool =
                if test
                {
                    let v10: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(c1);
                    let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                    let s: &[u8] =
                        match _letpattern0
                        {
                            crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                            _ => panic!("Incomplete pattern matching")
                        };
                    if s.len() != 9u64 as usize
                    { false }
                    else
                    {
                        let x: u8 = s[0usize];
                        let i·: usize = 1usize;
                        let res: bool =
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
                                                            if x8 == 101u8 { true } else { false }
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
                            { false };
                        res
                    }
                }
                else
                { false };
            let test1: bool =
                if test0
                { true }
                else
                {
                    let mt0: u8 = crate::cbordetver::cbor_det_major_type(c1);
                    let test1: bool = mt0 == crate::cbordetveraux::cbor_major_type_text_string;
                    if test1
                    {
                        let v10: crate::cbordetver::cbor_det_view =
                            crate::cbordetver::cbor_det_destruct(c1);
                        let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                        let s: &[u8] =
                            match _letpattern0
                            {
                                crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                                _ => panic!("Incomplete pattern matching")
                            };
                        if s.len() != 10u64 as usize
                        { false }
                        else
                        {
                            let x: u8 = s[0usize];
                            let i·: usize = 1usize;
                            let res: bool =
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
                                                            let i·7: usize =
                                                                i·6.wrapping_add(1usize);
                                                            if x7 == 114u8
                                                            {
                                                                let x8: u8 = s[i·7];
                                                                let i·8: usize =
                                                                    i·7.wrapping_add(1usize);
                                                                if x8 == 101u8
                                                                {
                                                                    let x9: u8 = s[i·8];
                                                                    if x9 == 49u8
                                                                    { true }
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
                                else
                                { false };
                            res
                        }
                    }
                    else
                    { false }
                };
            test1
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp);
    let c1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0];
    let rlen1: u64 = crate::cbordetver::cbor_det_array_iterator_length(c1);
    let c0·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(ar, rlen0.wrapping_sub(rlen1));
    let mut pc1: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·; 1usize];
    let x: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc1);
    let mt: u8 = crate::cbordetver::cbor_det_major_type(x);
    let test: bool = mt == crate::cbordetveraux::cbor_major_type_text_string;
    let test0: bool =
        if test
        {
            let v10: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(x);
            let _letpattern0: crate::cbordetver::cbor_det_view = v10;
            let s: &[u8] =
                match _letpattern0
                {
                    crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            if s.len() != 9u64 as usize
            { false }
            else
            {
                let x1: u8 = s[0usize];
                let i·: usize = 1usize;
                let res: bool =
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
                                                    if x9 == 101u8 { true } else { false }
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
                    { false };
                res
            }
        }
        else
        { false };
    let res: evercddl_int_tags =
        if test0 { evercddl_int_tags::Inl } else { evercddl_int_tags::Inr };
    let w1: evercddl_int_tags = res;
    let rlen01: u64 = crate::cbordetver::cbor_det_array_iterator_length(c1);
    let mut pc10: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c1; 1usize];
    let i0: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc10)[0];
    let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i0);
    let _tmp1: bool =
        if is_done0
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc10);
            let test1: bool = validate_empty_or_serialized_map(c2);
            test1
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp1);
    let c11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc10)[0];
    let rlen11: u64 = crate::cbordetver::cbor_det_array_iterator_length(c11);
    let c0·1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c1, rlen01.wrapping_sub(rlen11));
    let mut pc2: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·1; 1usize];
    let x0: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc2);
    let res0: evercddl_empty_or_serialized_map_pretty = parse_empty_or_serialized_map(x0);
    let w11: evercddl_empty_or_serialized_map_pretty = res0;
    let mut pc20: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c11; 1usize];
    let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc20)[0];
    let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
    let test1: bool =
        if is_done1
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc20);
            let test1: bool = validate_empty_or_serialized_map(c2);
            test1
        };
    let test10: bool =
        if test1
        {
            let i2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc20)[0];
            let is_done2: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
            let test11: bool =
                if is_done2
                { false }
                else
                {
                    let c2: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_array_iterator_next(&mut pc20);
                    let test2: bool = validate_bstr(c2);
                    test2
                };
            let test2: bool =
                if test11
                {
                    let i3: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                        (&pc20)[0];
                    let is_done3: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i3);
                    let test2: bool =
                        if is_done3
                        { false }
                        else
                        {
                            let c2: crate::cbordetveraux::cbor_raw =
                                crate::cbordetver::cbor_det_array_iterator_next(&mut pc20);
                            let test2: bool = validate_bstr(c2);
                            test2
                        };
                    test2
                }
                else
                { false };
            test2
        }
        else
        { false };
    let
    _bind_c:
    either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·
    =
        if test10
        {
            let rlen02: u64 = crate::cbordetver::cbor_det_array_iterator_length(c11);
            let
            mut pc3: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
            =
                [c11; 1usize];
            let i2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc3)[0];
            let is_done2: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
            let _tmp2: bool =
                if is_done2
                { false }
                else
                {
                    let c2: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_array_iterator_next(&mut pc3);
                    let test2: bool = validate_empty_or_serialized_map(c2);
                    test2
                };
            crate::lowstar::ignore::ignore::<bool>(_tmp2);
            let c12: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc3)[0];
            let rlen12: u64 = crate::cbordetver::cbor_det_array_iterator_length(c12);
            let c0·2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_truncate(
                    c11,
                    rlen02.wrapping_sub(rlen12)
                );
            let
            mut pc4: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
            =
                [c0·2; 1usize];
            let x1: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc4);
            let res1: evercddl_empty_or_serialized_map_pretty = parse_empty_or_serialized_map(x1);
            let w12: evercddl_empty_or_serialized_map_pretty = res1;
            let rlen03: u64 = crate::cbordetver::cbor_det_array_iterator_length(c12);
            let
            mut pc40: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
            =
                [c12; 1usize];
            let i3: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc40)[0];
            let is_done3: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i3);
            let _tmp3: bool =
                if is_done3
                { false }
                else
                {
                    let c2: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_array_iterator_next(&mut pc40);
                    let test2: bool = validate_bstr(c2);
                    test2
                };
            crate::lowstar::ignore::ignore::<bool>(_tmp3);
            let c13: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc40)[0];
            let rlen13: u64 = crate::cbordetver::cbor_det_array_iterator_length(c13);
            let c0·3: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_truncate(
                    c12,
                    rlen03.wrapping_sub(rlen13)
                );
            let
            mut pc5: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
            =
                [c0·3; 1usize];
            let x2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc5);
            let res2: &[u8] = parse_bstr(x2);
            let w13: &[u8] = res2;
            let
            mut pc50: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
            =
                [c13; 1usize];
            let x3: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc50);
            let res3: &[u8] = parse_bstr(x3);
            let w2: &[u8] = res3;
            let w20: (&[u8], &[u8]) = (w13,w2);
            let w120: (evercddl_empty_or_serialized_map_pretty, (&[u8], &[u8])) = (w12,w20);
            either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·::Inl
            { v: w120 }
        }
        else
        {
            let rlen02: u64 = crate::cbordetver::cbor_det_array_iterator_length(c11);
            let
            mut pc3: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
            =
                [c11; 1usize];
            let i2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc3)[0];
            let is_done2: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
            let _tmp2: bool =
                if is_done2
                { false }
                else
                {
                    let c2: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_array_iterator_next(&mut pc3);
                    let test2: bool = validate_bstr(c2);
                    test2
                };
            crate::lowstar::ignore::ignore::<bool>(_tmp2);
            let c12: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc3)[0];
            let rlen12: u64 = crate::cbordetver::cbor_det_array_iterator_length(c12);
            let c0·2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_truncate(
                    c11,
                    rlen02.wrapping_sub(rlen12)
                );
            let
            mut pc4: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
            =
                [c0·2; 1usize];
            let x1: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc4);
            let res1: &[u8] = parse_bstr(x1);
            let w12: &[u8] = res1;
            let
            mut pc40: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
            =
                [c12; 1usize];
            let x2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc40);
            let res2: &[u8] = parse_bstr(x2);
            let w2: &[u8] = res2;
            let w20: (&[u8], &[u8]) = (w12,w2);
            either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·::Inr
            { v: w20 }
        };
    let
    w2:
    either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·
    =
        _bind_c;
    let
    w20:
    (evercddl_empty_or_serialized_map_pretty,
    either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·)
    =
        (w11,w2);
    let
    res1:
    (evercddl_int_tags,
    (evercddl_empty_or_serialized_map_pretty,
    either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·))
    =
        (w1,w20);
    let
    res10:
    (evercddl_int_tags,
    (evercddl_empty_or_serialized_map_pretty,
    either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·))
    =
        res1;
    let res2: evercddl_Sig_structure_pretty = evercddl_Sig_structure_pretty_right(res10);
    res2
}

/**
Serializer for evercddl_Sig_structure
*/
pub fn
serialize_Sig_structure(c: evercddl_Sig_structure_pretty, out: &mut [u8]) ->
    usize
{
    let
    c·:
    (evercddl_int_tags,
    (evercddl_empty_or_serialized_map_pretty,
    either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·))
    =
        evercddl_Sig_structure_pretty_left(c);
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let
    _letpattern:
    (evercddl_int_tags,
    (evercddl_empty_or_serialized_map_pretty,
    either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·))
    =
        c·;
    let res: bool =
        {
            let c1: evercddl_int_tags = _letpattern.0;
            let
            c2:
            (evercddl_empty_or_serialized_map_pretty,
            either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·)
            =
                _letpattern.1;
            let count: u64 = (&pcount)[0];
            let res1: bool =
                if count < 18446744073709551615u64
                {
                    let size: usize = (&psize)[0];
                    let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                    let _out0: &[u8] = _letpattern1.0;
                    let out1: &mut [u8] = _letpattern1.1;
                    let size1: usize =
                        match c1
                        {
                            evercddl_int_tags::Inl =>
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
                                  let
                                  _letpattern2:
                                  crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                  =
                                      res;
                                  let c3: crate::cbordetveraux::cbor_raw =
                                      match _letpattern2
                                      {
                                          crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                          { v: c3 }
                                          => c3,
                                          _ => panic!("Incomplete pattern matching")
                                      };
                                  let res0: crate::cbordetver::option__size_t =
                                      crate::cbordetver::cbor_det_serialize(c3, out1);
                                  let res1: usize =
                                      match res0
                                      {
                                          crate::cbordetver::option__size_t::None => 0usize,
                                          crate::cbordetver::option__size_t::Some { v: r } => r,
                                          _ => panic!("Incomplete pattern matching")
                                      };
                                  let res2: usize = res1;
                                  res2
                              },
                            evercddl_int_tags::Inr =>
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
                                  let
                                  _letpattern2:
                                  crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                  =
                                      res;
                                  let c3: crate::cbordetveraux::cbor_raw =
                                      match _letpattern2
                                      {
                                          crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                          { v: c3 }
                                          => c3,
                                          _ => panic!("Incomplete pattern matching")
                                      };
                                  let res0: crate::cbordetver::option__size_t =
                                      crate::cbordetver::cbor_det_serialize(c3, out1);
                                  let res1: usize =
                                      match res0
                                      {
                                          crate::cbordetver::option__size_t::None => 0usize,
                                          crate::cbordetver::option__size_t::Some { v: r } => r,
                                          _ => panic!("Incomplete pattern matching")
                                      };
                                  let res2: usize = res1;
                                  res2
                              },
                            _ => panic!("Precondition of the function most likely violated")
                        };
                    if size1 == 0usize
                    { false }
                    else
                    {
                        (&mut pcount)[0] = count.wrapping_add(1u64);
                        (&mut psize)[0] = size.wrapping_add(size1);
                        true
                    }
                }
                else
                { false };
            if res1
            {
                let
                _letpattern1:
                (evercddl_empty_or_serialized_map_pretty,
                either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·)
                =
                    c2;
                let res2: bool =
                    {
                        let c11: evercddl_empty_or_serialized_map_pretty = _letpattern1.0;
                        let
                        c21:
                        either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·
                        =
                            _letpattern1.1;
                        let count0: u64 = (&pcount)[0];
                        let res11: bool =
                            if count0 < 18446744073709551615u64
                            {
                                let size: usize = (&psize)[0];
                                let _letpattern2: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                                let _out0: &[u8] = _letpattern2.0;
                                let out1: &mut [u8] = _letpattern2.1;
                                let size1: usize = serialize_empty_or_serialized_map(c11, out1);
                                if size1 == 0usize
                                { false }
                                else
                                {
                                    (&mut pcount)[0] = count0.wrapping_add(1u64);
                                    (&mut psize)[0] = size.wrapping_add(size1);
                                    true
                                }
                            }
                            else
                            { false };
                        if res11
                        {
                            let res2: bool =
                                match c21
                                {
                                    either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·::Inl
                                    { v: c12 }
                                    =>
                                      {
                                          let
                                          _letpattern2:
                                          (evercddl_empty_or_serialized_map_pretty, (&[u8], &[u8]))
                                          =
                                              c12;
                                          let res: bool =
                                              {
                                                  let c13: evercddl_empty_or_serialized_map_pretty =
                                                      _letpattern2.0;
                                                  let c22: (&[u8], &[u8]) = _letpattern2.1;
                                                  let count1: u64 = (&pcount)[0];
                                                  let res12: bool =
                                                      if count1 < 18446744073709551615u64
                                                      {
                                                          let size: usize = (&psize)[0];
                                                          let _letpattern3: (&mut [u8], &mut [u8]) =
                                                              out.split_at_mut(size);
                                                          let _out0: &[u8] = _letpattern3.0;
                                                          let out1: &mut [u8] = _letpattern3.1;
                                                          let size1: usize =
                                                              serialize_empty_or_serialized_map(
                                                                  c13,
                                                                  out1
                                                              );
                                                          if size1 == 0usize
                                                          { false }
                                                          else
                                                          {
                                                              (&mut pcount)[0] =
                                                                  count1.wrapping_add(1u64);
                                                              (&mut psize)[0] =
                                                                  size.wrapping_add(size1);
                                                              true
                                                          }
                                                      }
                                                      else
                                                      { false };
                                                  if res12
                                                  {
                                                      let _letpattern3: (&[u8], &[u8]) = c22;
                                                      let res2: bool =
                                                          {
                                                              let c14: &[u8] = _letpattern3.0;
                                                              let c23: &[u8] = _letpattern3.1;
                                                              let count2: u64 = (&pcount)[0];
                                                              let res13: bool =
                                                                  if
                                                                  count2 < 18446744073709551615u64
                                                                  {
                                                                      let size: usize = (&psize)[0];
                                                                      let
                                                                      _letpattern4:
                                                                      (&mut [u8], &mut [u8])
                                                                      =
                                                                          out.split_at_mut(size);
                                                                      let _out0: &[u8] =
                                                                          _letpattern4.0;
                                                                      let out1: &mut [u8] =
                                                                          _letpattern4.1;
                                                                      let size1: usize =
                                                                          serialize_bstr(c14, out1);
                                                                      if size1 == 0usize
                                                                      { false }
                                                                      else
                                                                      {
                                                                          (&mut pcount)[0] =
                                                                              count2.wrapping_add(
                                                                                  1u64
                                                                              );
                                                                          (&mut psize)[0] =
                                                                              size.wrapping_add(
                                                                                  size1
                                                                              );
                                                                          true
                                                                      }
                                                                  }
                                                                  else
                                                                  { false };
                                                              if res13
                                                              {
                                                                  let count3: u64 = (&pcount)[0];
                                                                  let res2: bool =
                                                                      if
                                                                      count3
                                                                      <
                                                                      18446744073709551615u64
                                                                      {
                                                                          let size: usize =
                                                                              (&psize)[0];
                                                                          let
                                                                          _letpattern4:
                                                                          (&mut [u8], &mut [u8])
                                                                          =
                                                                              out.split_at_mut(size);
                                                                          let _out0: &[u8] =
                                                                              _letpattern4.0;
                                                                          let out1: &mut [u8] =
                                                                              _letpattern4.1;
                                                                          let size1: usize =
                                                                              serialize_bstr(
                                                                                  c23,
                                                                                  out1
                                                                              );
                                                                          if size1 == 0usize
                                                                          { false }
                                                                          else
                                                                          {
                                                                              (&mut pcount)[0] =
                                                                                  count3.wrapping_add(
                                                                                      1u64
                                                                                  );
                                                                              (&mut psize)[0] =
                                                                                  size.wrapping_add(
                                                                                      size1
                                                                                  );
                                                                              true
                                                                          }
                                                                      }
                                                                      else
                                                                      { false };
                                                                  res2
                                                              }
                                                              else
                                                              { false }
                                                          };
                                                      res2
                                                  }
                                                  else
                                                  { false }
                                              };
                                          res
                                      },
                                    either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·::Inr
                                    { v: c22 }
                                    =>
                                      {
                                          let _letpattern2: (&[u8], &[u8]) = c22;
                                          let res: bool =
                                              {
                                                  let c12: &[u8] = _letpattern2.0;
                                                  let c23: &[u8] = _letpattern2.1;
                                                  let count1: u64 = (&pcount)[0];
                                                  let res12: bool =
                                                      if count1 < 18446744073709551615u64
                                                      {
                                                          let size: usize = (&psize)[0];
                                                          let _letpattern3: (&mut [u8], &mut [u8]) =
                                                              out.split_at_mut(size);
                                                          let _out0: &[u8] = _letpattern3.0;
                                                          let out1: &mut [u8] = _letpattern3.1;
                                                          let size1: usize =
                                                              serialize_bstr(c12, out1);
                                                          if size1 == 0usize
                                                          { false }
                                                          else
                                                          {
                                                              (&mut pcount)[0] =
                                                                  count1.wrapping_add(1u64);
                                                              (&mut psize)[0] =
                                                                  size.wrapping_add(size1);
                                                              true
                                                          }
                                                      }
                                                      else
                                                      { false };
                                                  if res12
                                                  {
                                                      let count2: u64 = (&pcount)[0];
                                                      let res2: bool =
                                                          if count2 < 18446744073709551615u64
                                                          {
                                                              let size: usize = (&psize)[0];
                                                              let
                                                              _letpattern3: (&mut [u8], &mut [u8])
                                                              =
                                                                  out.split_at_mut(size);
                                                              let _out0: &[u8] = _letpattern3.0;
                                                              let out1: &mut [u8] = _letpattern3.1;
                                                              let size1: usize =
                                                                  serialize_bstr(c23, out1);
                                                              if size1 == 0usize
                                                              { false }
                                                              else
                                                              {
                                                                  (&mut pcount)[0] =
                                                                      count2.wrapping_add(1u64);
                                                                  (&mut psize)[0] =
                                                                      size.wrapping_add(size1);
                                                                  true
                                                              }
                                                          }
                                                          else
                                                          { false };
                                                      res2
                                                  }
                                                  else
                                                  { false }
                                              };
                                          res
                                      },
                                    _ => panic!("Incomplete pattern matching")
                                };
                            res2
                        }
                        else
                        { false }
                    };
                res2
            }
            else
            { false }
        };
    let _bind_c: usize =
        if res
        {
            let size: usize = (&psize)[0];
            let count: u64 = (&pcount)[0];
            crate::cbordetver::cbor_det_serialize_array(count, out, size)
        }
        else
        { 0usize };
    let res0: usize = _bind_c;
    res0
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_Sig_structure_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_Sig_structure_pretty <'a>, &'a [u8]) }
}

pub fn validate_and_parse_Sig_structure <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_Sig_structure_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_Sig_structure_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_Sig_structure(rl);
              if test
              {
                  let x: evercddl_Sig_structure_pretty = parse_Sig_structure(rl);
                  option__·COSE_Format_evercddl_Sig_structure_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_Sig_structure_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_Internal_Types(c: crate::cbordetveraux::cbor_raw) -> bool
{ validate_Sig_structure(c) }

pub type evercddl_Internal_Types_pretty <'a> = evercddl_Sig_structure_pretty <'a>;

pub fn uu___is_Mkevercddl_Internal_Types_pretty0(projectee: evercddl_Sig_structure_pretty) ->
    bool
{
    crate::lowstar::ignore::ignore::<evercddl_Sig_structure_pretty>(projectee);
    true
}

fn evercddl_Internal_Types_pretty_right <'a>(x1: evercddl_Sig_structure_pretty <'a>) ->
    evercddl_Sig_structure_pretty
    <'a>
{ x1 }

fn evercddl_Internal_Types_pretty_left <'a>(x3: evercddl_Sig_structure_pretty <'a>) ->
    evercddl_Sig_structure_pretty
    <'a>
{ x3 }

/**
Parser for evercddl_Internal_Types
*/
pub fn
parse_Internal_Types
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_Sig_structure_pretty
    <'a>
{
    let res1: evercddl_Sig_structure_pretty = parse_Sig_structure(c);
    let res2: evercddl_Sig_structure_pretty = evercddl_Internal_Types_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_Internal_Types
*/
pub fn
serialize_Internal_Types(c: evercddl_Sig_structure_pretty, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_Sig_structure_pretty = evercddl_Internal_Types_pretty_left(c);
    let res: usize = serialize_Sig_structure(c·, out);
    res
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_Internal_Types_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_Sig_structure_pretty <'a>, &'a [u8]) }
}

pub fn validate_and_parse_Internal_Types <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_Internal_Types_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_Internal_Types_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_Internal_Types(rl);
              if test
              {
                  let x: evercddl_Sig_structure_pretty = parse_Internal_Types(rl);
                  option__·COSE_Format_evercddl_Internal_Types_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_Internal_Types_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_start(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let test: bool = validate_COSE_Messages(c);
    if test { true } else { validate_Internal_Types(c) }
}

#[derive(PartialEq, Clone, Copy)]
enum evercddl_start <'a>
{
    Inl { v: evercddl_COSE_Messages_pretty <'a> },
    Inr { v: evercddl_Sig_structure_pretty <'a> }
}

#[derive(PartialEq, Clone, Copy)]
enum evercddl_start_pretty_tags
{
    Mkevercddl_start_pretty0,
    Mkevercddl_start_pretty1
}

#[derive(PartialEq, Clone, Copy)]
pub enum evercddl_start_pretty <'a>
{
    Mkevercddl_start_pretty0 { _x0: evercddl_COSE_Messages_pretty <'a> },
    Mkevercddl_start_pretty1 { _x0: evercddl_Sig_structure_pretty <'a> }
}

pub fn uu___is_Mkevercddl_start_pretty0(projectee: evercddl_start_pretty) -> bool
{
    match projectee { evercddl_start_pretty::Mkevercddl_start_pretty0 { .. } => true, _ => false }
}

pub fn uu___is_Mkevercddl_start_pretty1(projectee: evercddl_start_pretty) -> bool
{
    match projectee { evercddl_start_pretty::Mkevercddl_start_pretty1 { .. } => true, _ => false }
}

fn evercddl_start_pretty_right <'a>(x2: evercddl_start <'a>) -> evercddl_start_pretty <'a>
{
    match x2
    {
        evercddl_start::Inl { v: x3 } => evercddl_start_pretty::Mkevercddl_start_pretty0 { _x0: x3 },
        evercddl_start::Inr { v: x4 } => evercddl_start_pretty::Mkevercddl_start_pretty1 { _x0: x4 },
        _ => panic!("Incomplete pattern matching")
    }
}

fn evercddl_start_pretty_left <'a>(x7: evercddl_start_pretty <'a>) -> evercddl_start <'a>
{
    match x7
    {
        evercddl_start_pretty::Mkevercddl_start_pretty0 { _x0: x10 } =>
          evercddl_start::Inl { v: x10 },
        evercddl_start_pretty::Mkevercddl_start_pretty1 { _x0: x12 } =>
          evercddl_start::Inr { v: x12 },
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Parser for evercddl_start
*/
pub fn
parse_start
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_start_pretty
    <'a>
{
    let test: bool = validate_COSE_Messages(c);
    let res1: evercddl_start =
        if test
        {
            let res: evercddl_COSE_Messages_pretty = parse_COSE_Messages(c);
            evercddl_start::Inl { v: res }
        }
        else
        {
            let res: evercddl_Sig_structure_pretty = parse_Internal_Types(c);
            evercddl_start::Inr { v: res }
        };
    let res2: evercddl_start_pretty = evercddl_start_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_start
*/
pub fn
serialize_start(c: evercddl_start_pretty, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_start = evercddl_start_pretty_left(c);
    match c·
    {
        evercddl_start::Inl { v: c1 } =>
          {
              let res: usize = serialize_COSE_Messages(c1, out);
              res
          },
        evercddl_start::Inr { v: c2 } =>
          {
              let res: usize = serialize_Internal_Types(c2, out);
              res
          },
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_start_pretty···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_start_pretty <'a>, &'a [u8]) }
}

pub fn validate_and_parse_start <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_start_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_start_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_start(rl);
              if test
              {
                  let x: evercddl_start_pretty = parse_start(rl);
                  option__·COSE_Format_evercddl_start_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_start_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn aux_env39_validate_1(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;
    let test: bool =
        if is_uint
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern: crate::cbordetver::cbor_det_view = v1;
            let i: u64 =
                match _letpattern
                {
                    crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                    _ => panic!("Incomplete pattern matching")
                };
            i == 1u64
        }
        else
        { false };
    let test0: bool =
        if test
        { true }
        else
        {
            let mt0: u8 = crate::cbordetver::cbor_det_major_type(c);
            let is_uint0: bool = mt0 == crate::cbordetveraux::cbor_major_type_neg_int64;
            if is_uint0
            {
                let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
                let _letpattern: crate::cbordetver::cbor_det_view = v1;
                let i: u64 =
                    match _letpattern
                    {
                        crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                        _ => panic!("Incomplete pattern matching")
                    };
                i == 0u64
            }
            else
            { false }
        };
    let test1: bool =
        if test0
        { true }
        else
        {
            let mt0: u8 = crate::cbordetver::cbor_det_major_type(c);
            let is_uint0: bool = mt0 == crate::cbordetveraux::cbor_major_type_neg_int64;
            if is_uint0
            {
                let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
                let _letpattern: crate::cbordetver::cbor_det_view = v1;
                let i: u64 =
                    match _letpattern
                    {
                        crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                        _ => panic!("Incomplete pattern matching")
                    };
                i == 1u64
            }
            else
            { false }
        };
    if test1
    { true }
    else
    {
        let mt0: u8 = crate::cbordetver::cbor_det_major_type(c);
        let is_uint0: bool = mt0 == crate::cbordetveraux::cbor_major_type_neg_int64;
        if is_uint0
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern: crate::cbordetver::cbor_det_view = v1;
            let i: u64 =
                match _letpattern
                {
                    crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                    _ => panic!("Incomplete pattern matching")
                };
            i == 3u64
        }
        else
        { false }
    }
}

pub fn validate_COSE_Key_OKP(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let ty: u8 = crate::cbordetver::cbor_det_major_type(c);
    if ty == crate::cbordetveraux::cbor_major_type_map
    {
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let rem0: u64 =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Map { _0: a } =>
                  {
                      let res: u64 = crate::cbordetver::cbor_det_map_length(a);
                      res
                  },
                _ => panic!("Incomplete pattern matching")
            };
        let mut remaining: [u64; 1] = [rem0; 1usize];
        let mty: crate::cbordetver::cbor_det_int_kind =
            crate::cbordetver::cbor_det_int_kind::UInt64;
        let c1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty, 1u64);
        let x·: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern0: crate::cbordetver::cbor_det_view = x·;
        let mg: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
            match _letpattern0
            {
                crate::cbordetver::cbor_det_view::Map { _0: m1 } =>
                  {
                      let res: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                          crate::cbordetver::cbor_det_map_get(m1, c1);
                      res
                  },
                _ => panic!("Incomplete pattern matching")
            };
        let res: crate::cbordetveraux::impl_map_group_result =
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
                              let v10: crate::cbordetver::cbor_det_view =
                                  crate::cbordetver::cbor_det_destruct(cv);
                              let _letpattern1: crate::cbordetver::cbor_det_view = v10;
                              let i: u64 =
                                  match _letpattern1
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
                          let i1: u64 = (&remaining)[0];
                          let i2: u64 = i1.wrapping_sub(1u64);
                          (&mut remaining)[0] = i2;
                          crate::cbordetveraux::impl_map_group_result::MGOK
                      }
                      else
                      { crate::cbordetveraux::impl_map_group_result::MGCutFail }
                  },
                _ => panic!("Incomplete pattern matching")
            };
        let res0: crate::cbordetveraux::impl_map_group_result = res;
        let res1: crate::cbordetveraux::impl_map_group_result = res0;
        let res10: crate::cbordetveraux::impl_map_group_result =
            match res1
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  {
                      let mty0: crate::cbordetver::cbor_det_int_kind =
                          if
                          crate::cbordetveraux::cbor_major_type_neg_int64
                          ==
                          crate::cbordetveraux::cbor_major_type_uint64
                          { crate::cbordetver::cbor_det_int_kind::UInt64 }
                          else
                          { crate::cbordetver::cbor_det_int_kind::NegInt64 };
                      let c10: crate::cbordetveraux::cbor_raw =
                          crate::cbordetver::cbor_det_mk_int64(mty0, 0u64);
                      let x·0: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let _letpattern1: crate::cbordetver::cbor_det_view = x·0;
                      let mg0: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                          match _letpattern1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: m2 } =>
                                {
                                    let
                                    res2: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                    =
                                        crate::cbordetver::cbor_det_map_get(m2, c10);
                                    res2
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res2: crate::cbordetveraux::impl_map_group_result =
                          match mg0
                          {
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::None =>
                                crate::cbordetveraux::impl_map_group_result::MGFail,
                              crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                              { v: cv }
                              =>
                                {
                                    let test: bool = validate_int(cv);
                                    let check_value: bool =
                                        if test { true } else { validate_tstr(cv) };
                                    if check_value
                                    {
                                        let i1: u64 = (&remaining)[0];
                                        let i2: u64 = i1.wrapping_sub(1u64);
                                        (&mut remaining)[0] = i2;
                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                    }
                                    else
                                    { crate::cbordetveraux::impl_map_group_result::MGCutFail }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res3: crate::cbordetveraux::impl_map_group_result = res2;
                      let res4: crate::cbordetveraux::impl_map_group_result = res3;
                      res4
                  },
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        let res11: crate::cbordetveraux::impl_map_group_result =
            match res10
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  {
                      let i0: u64 = (&remaining)[0];
                      let mty0: crate::cbordetver::cbor_det_int_kind =
                          if
                          crate::cbordetveraux::cbor_major_type_neg_int64
                          ==
                          crate::cbordetveraux::cbor_major_type_uint64
                          { crate::cbordetver::cbor_det_int_kind::UInt64 }
                          else
                          { crate::cbordetver::cbor_det_int_kind::NegInt64 };
                      let c10: crate::cbordetveraux::cbor_raw =
                          crate::cbordetver::cbor_det_mk_int64(mty0, 1u64);
                      let x·0: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let _letpattern1: crate::cbordetver::cbor_det_view = x·0;
                      let mg0: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                          match _letpattern1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: m2 } =>
                                {
                                    let
                                    res2: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                    =
                                        crate::cbordetver::cbor_det_map_get(m2, c10);
                                    res2
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res2: crate::cbordetveraux::impl_map_group_result =
                          match mg0
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
                                        let i1: u64 = (&remaining)[0];
                                        let i2: u64 = i1.wrapping_sub(1u64);
                                        (&mut remaining)[0] = i2;
                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                    }
                                    else
                                    { crate::cbordetveraux::impl_map_group_result::MGCutFail }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res3: crate::cbordetveraux::impl_map_group_result = res2;
                      let res11: crate::cbordetveraux::impl_map_group_result = res3;
                      let res4: crate::cbordetveraux::impl_map_group_result =
                          match res11
                          {
                              crate::cbordetveraux::impl_map_group_result::MGOK =>
                                crate::cbordetveraux::impl_map_group_result::MGOK,
                              crate::cbordetveraux::impl_map_group_result::MGFail =>
                                {
                                    (&mut remaining)[0] = i0;
                                    crate::cbordetveraux::impl_map_group_result::MGOK
                                },
                              crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                                crate::cbordetveraux::impl_map_group_result::MGCutFail,
                              _ => panic!("Precondition of the function most likely violated")
                          };
                      res4
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
                      let i0: u64 = (&remaining)[0];
                      let mty0: crate::cbordetver::cbor_det_int_kind =
                          if
                          crate::cbordetveraux::cbor_major_type_neg_int64
                          ==
                          crate::cbordetveraux::cbor_major_type_uint64
                          { crate::cbordetver::cbor_det_int_kind::UInt64 }
                          else
                          { crate::cbordetver::cbor_det_int_kind::NegInt64 };
                      let c10: crate::cbordetveraux::cbor_raw =
                          crate::cbordetver::cbor_det_mk_int64(mty0, 3u64);
                      let x·0: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let _letpattern1: crate::cbordetver::cbor_det_view = x·0;
                      let mg0: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                          match _letpattern1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: m2 } =>
                                {
                                    let
                                    res2: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                    =
                                        crate::cbordetver::cbor_det_map_get(m2, c10);
                                    res2
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res2: crate::cbordetveraux::impl_map_group_result =
                          match mg0
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
                                        let i1: u64 = (&remaining)[0];
                                        let i2: u64 = i1.wrapping_sub(1u64);
                                        (&mut remaining)[0] = i2;
                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                    }
                                    else
                                    { crate::cbordetveraux::impl_map_group_result::MGCutFail }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res3: crate::cbordetveraux::impl_map_group_result = res2;
                      let res110: crate::cbordetveraux::impl_map_group_result = res3;
                      let res4: crate::cbordetveraux::impl_map_group_result =
                          match res110
                          {
                              crate::cbordetveraux::impl_map_group_result::MGOK =>
                                crate::cbordetveraux::impl_map_group_result::MGOK,
                              crate::cbordetveraux::impl_map_group_result::MGFail =>
                                {
                                    (&mut remaining)[0] = i0;
                                    crate::cbordetveraux::impl_map_group_result::MGOK
                                },
                              crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                                crate::cbordetveraux::impl_map_group_result::MGCutFail,
                              _ => panic!("Precondition of the function most likely violated")
                          };
                      res4
                  },
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        let res2: crate::cbordetveraux::impl_map_group_result =
            match res12
            {
                crate::cbordetveraux::impl_map_group_result::MGOK =>
                  {
                      let v10: crate::cbordetver::cbor_det_view =
                          crate::cbordetver::cbor_det_destruct(c);
                      let _letpattern1: crate::cbordetver::cbor_det_view = v10;
                      let
                      j0:
                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                      =
                          match _letpattern1
                          {
                              crate::cbordetver::cbor_det_view::Map { _0: a } =>
                                {
                                    let
                                    res2:
                                    crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                    =
                                        crate::cbordetver::cbor_det_map_iterator_start(a);
                                    res2
                                },
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
                          (&pj)[0];
                      let is_empty: bool = crate::cbordetver::cbor_det_map_iterator_is_empty(j);
                      let mut cond: bool = ! is_empty;
                      while
                      cond
                      {
                          let chd: crate::cbordetveraux::cbor_map_entry =
                              crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
                          let k: crate::cbordetveraux::cbor_raw =
                              crate::cbordetver::cbor_det_map_entry_key(chd);
                          let test1: bool = validate_label(k);
                          let testk: bool =
                              if test1
                              {
                                  let mt: u8 = crate::cbordetver::cbor_det_major_type(k);
                                  let is_uint: bool =
                                      mt == crate::cbordetveraux::cbor_major_type_uint64;
                                  let test: bool =
                                      if is_uint
                                      {
                                          let v11: crate::cbordetver::cbor_det_view =
                                              crate::cbordetver::cbor_det_destruct(k);
                                          let _letpattern2: crate::cbordetver::cbor_det_view = v11;
                                          let i: u64 =
                                              match _letpattern2
                                              {
                                                  crate::cbordetver::cbor_det_view::Int64
                                                  { value: res2, .. }
                                                  => res2,
                                                  _ => panic!("Incomplete pattern matching")
                                              };
                                          i == 1u64
                                      }
                                      else
                                      { false };
                                  let test0: bool =
                                      if test
                                      { true }
                                      else
                                      {
                                          let mt0: u8 = crate::cbordetver::cbor_det_major_type(k);
                                          let is_uint0: bool =
                                              mt0 == crate::cbordetveraux::cbor_major_type_neg_int64;
                                          if is_uint0
                                          {
                                              let v11: crate::cbordetver::cbor_det_view =
                                                  crate::cbordetver::cbor_det_destruct(k);
                                              let _letpattern2: crate::cbordetver::cbor_det_view =
                                                  v11;
                                              let i: u64 =
                                                  match _letpattern2
                                                  {
                                                      crate::cbordetver::cbor_det_view::Int64
                                                      { value: res2, .. }
                                                      => res2,
                                                      _ => panic!("Incomplete pattern matching")
                                                  };
                                              i == 0u64
                                          }
                                          else
                                          { false }
                                      };
                                  let test2: bool =
                                      if test0
                                      { true }
                                      else
                                      {
                                          let mt0: u8 = crate::cbordetver::cbor_det_major_type(k);
                                          let is_uint0: bool =
                                              mt0 == crate::cbordetveraux::cbor_major_type_neg_int64;
                                          if is_uint0
                                          {
                                              let v11: crate::cbordetver::cbor_det_view =
                                                  crate::cbordetver::cbor_det_destruct(k);
                                              let _letpattern2: crate::cbordetver::cbor_det_view =
                                                  v11;
                                              let i: u64 =
                                                  match _letpattern2
                                                  {
                                                      crate::cbordetver::cbor_det_view::Int64
                                                      { value: res2, .. }
                                                      => res2,
                                                      _ => panic!("Incomplete pattern matching")
                                                  };
                                              i == 1u64
                                          }
                                          else
                                          { false }
                                      };
                                  let test3: bool =
                                      if test2
                                      { true }
                                      else
                                      {
                                          let mt0: u8 = crate::cbordetver::cbor_det_major_type(k);
                                          let is_uint0: bool =
                                              mt0 == crate::cbordetveraux::cbor_major_type_neg_int64;
                                          if is_uint0
                                          {
                                              let v11: crate::cbordetver::cbor_det_view =
                                                  crate::cbordetver::cbor_det_destruct(k);
                                              let _letpattern2: crate::cbordetver::cbor_det_view =
                                                  v11;
                                              let i: u64 =
                                                  match _letpattern2
                                                  {
                                                      crate::cbordetver::cbor_det_view::Int64
                                                      { value: res2, .. }
                                                      => res2,
                                                      _ => panic!("Incomplete pattern matching")
                                                  };
                                              i == 3u64
                                          }
                                          else
                                          { false }
                                      };
                                  ! test3
                              }
                              else
                              { false };
                          let test: bool =
                              if testk
                              {
                                  let v11: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_value(chd);
                                  let testv: bool = validate_values(v11);
                                  testv
                              }
                              else
                              { false };
                          let test0: bool = ! test;
                          if ! test0
                          {
                              let i: u64 = (&remaining)[0];
                              let i·: u64 = i.wrapping_sub(1u64);
                              (&mut remaining)[0] = i·
                          };
                          let
                          j1:
                          crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                          =
                              (&pj)[0];
                          let is_empty0: bool =
                              crate::cbordetver::cbor_det_map_iterator_is_empty(j1);
                          cond = ! is_empty0
                      };
                      let res2: crate::cbordetveraux::impl_map_group_result =
                          crate::cbordetveraux::impl_map_group_result::MGOK;
                      res2
                  },
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        match res2
        {
            crate::cbordetveraux::impl_map_group_result::MGOK =>
              {
                  let rem: u64 = (&remaining)[0];
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
pub struct evercddl_COSE_Key_OKP_pretty <'a>
{
    pub intkeyneg1: evercddl_label <'a>,
    pub intkeyneg2: option__COSE_Format_evercddl_bstr_pretty <'a>,
    pub intkeyneg4: option__COSE_Format_evercddl_bstr_pretty <'a>,
    pub _x0:
    either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty
    <'a>
}

pub fn uu___is_Mkevercddl_COSE_Key_OKP_pretty0(projectee: evercddl_COSE_Key_OKP_pretty) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_COSE_Key_OKP_pretty>(projectee);
    true
}

fn evercddl_COSE_Key_OKP_pretty_right <'a>(
    x5:
    (((((), evercddl_label <'a>), option__COSE_Format_evercddl_bstr_pretty <'a>),
    option__COSE_Format_evercddl_bstr_pretty
    <'a>),
    either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty
    <'a>)
) ->
    evercddl_COSE_Key_OKP_pretty
    <'a>
{
    match x5
    {
        ((((_x6,x7),x8),x9),x10) =>
          evercddl_COSE_Key_OKP_pretty { intkeyneg1: x7, intkeyneg2: x8, intkeyneg4: x9, _x0: x10 }
    }
}

fn evercddl_COSE_Key_OKP_pretty_left <'a>(x11: evercddl_COSE_Key_OKP_pretty <'a>) ->
    (((((), evercddl_label <'a>), option__COSE_Format_evercddl_bstr_pretty <'a>),
    option__COSE_Format_evercddl_bstr_pretty
    <'a>),
    either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty
    <'a>)
{
    let x19: evercddl_label = x11.intkeyneg1;
    let x20: option__COSE_Format_evercddl_bstr_pretty = x11.intkeyneg2;
    let x21: option__COSE_Format_evercddl_bstr_pretty = x11.intkeyneg4;
    let
    x22:
    either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty
    =
        x11._x0;
    (((((),x19),x20),x21),x22)
}

/**
Parser for evercddl_COSE_Key_OKP
*/
pub fn
parse_COSE_Key_OKP
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_COSE_Key_OKP_pretty
    <'a>
{
    let mty: crate::cbordetver::cbor_det_int_kind = crate::cbordetver::cbor_det_int_kind::UInt64;
    let c1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty, 1u64);
    let x·: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = x·;
    let ow: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
              {
                  let res: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                      crate::cbordetver::cbor_det_map_get(m3, c1);
                  res
              },
            _ => panic!("Incomplete pattern matching")
        };
    let _letpattern0: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow;
    match _letpattern0
    {
        crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { .. } => (),
        _ => panic!("Incomplete pattern matching")
    };
    let mty0: crate::cbordetver::cbor_det_int_kind =
        if
        crate::cbordetveraux::cbor_major_type_neg_int64
        ==
        crate::cbordetveraux::cbor_major_type_uint64
        { crate::cbordetver::cbor_det_int_kind::UInt64 }
        else
        { crate::cbordetver::cbor_det_int_kind::NegInt64 };
    let c10: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty0, 0u64);
    let x·0: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern1: crate::cbordetver::cbor_det_view = x·0;
    let ow0: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern1
        {
            crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
              {
                  let res: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                      crate::cbordetver::cbor_det_map_get(m3, c10);
                  res
              },
            _ => panic!("Incomplete pattern matching")
        };
    let _letpattern2: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow0;
    let res: evercddl_label =
        match _letpattern2
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
              {
                  let test: bool = validate_int(w);
                  let res: evercddl_label =
                      if test
                      {
                          let res: evercddl_int_pretty = parse_int(w);
                          evercddl_label::Inl { v: res }
                      }
                      else
                      {
                          let res: &[u8] = parse_tstr(w);
                          evercddl_label::Inr { v: res }
                      };
                  res
              },
            _ => panic!("Incomplete pattern matching")
        };
    let w2: evercddl_label = res;
    let w1: ((), evercddl_label) = ((),w2);
    let dummy: [u64; 1] = [0u64; 1usize];
    crate::lowstar::ignore::ignore::<&[u64]>(&dummy);
    let mty1: crate::cbordetver::cbor_det_int_kind =
        if
        crate::cbordetveraux::cbor_major_type_neg_int64
        ==
        crate::cbordetveraux::cbor_major_type_uint64
        { crate::cbordetver::cbor_det_int_kind::UInt64 }
        else
        { crate::cbordetver::cbor_det_int_kind::NegInt64 };
    let c11: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty1, 1u64);
    let x·1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern3: crate::cbordetver::cbor_det_view = x·1;
    let mg: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern3
        {
            crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
              {
                  let res0: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                      crate::cbordetver::cbor_det_map_get(m3, c11);
                  res0
              },
            _ => panic!("Incomplete pattern matching")
        };
    let res0: crate::cbordetveraux::impl_map_group_result =
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
    let res1: crate::cbordetveraux::impl_map_group_result = res0;
    let test1: crate::cbordetveraux::impl_map_group_result = res1;
    let _bind_c: option__COSE_Format_evercddl_bstr_pretty =
        if crate::cbordetveraux::uu___is_MGOK(test1)
        {
            let mty2: crate::cbordetver::cbor_det_int_kind =
                if
                crate::cbordetveraux::cbor_major_type_neg_int64
                ==
                crate::cbordetveraux::cbor_major_type_uint64
                { crate::cbordetver::cbor_det_int_kind::UInt64 }
                else
                { crate::cbordetver::cbor_det_int_kind::NegInt64 };
            let c12: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty2, 1u64);
            let x·2: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern4: crate::cbordetver::cbor_det_view = x·2;
            let ow1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match _letpattern4
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
                      {
                          let res2: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                              crate::cbordetver::cbor_det_map_get(m3, c12);
                          res2
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            let _letpattern5: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow1;
            let res2: &[u8] =
                match _letpattern5
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      {
                          let res2: &[u8] = parse_bstr(w);
                          res2
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            let w11: &[u8] = res2;
            option__COSE_Format_evercddl_bstr_pretty::Some { v: w11 }
        }
        else
        { option__COSE_Format_evercddl_bstr_pretty::None };
    let w20: option__COSE_Format_evercddl_bstr_pretty = _bind_c;
    let w10: (((), evercddl_label), option__COSE_Format_evercddl_bstr_pretty) = (w1,w20);
    let dummy0: [u64; 1] = [0u64; 1usize];
    crate::lowstar::ignore::ignore::<&[u64]>(&dummy0);
    let mty2: crate::cbordetver::cbor_det_int_kind =
        if
        crate::cbordetveraux::cbor_major_type_neg_int64
        ==
        crate::cbordetveraux::cbor_major_type_uint64
        { crate::cbordetver::cbor_det_int_kind::UInt64 }
        else
        { crate::cbordetver::cbor_det_int_kind::NegInt64 };
    let c12: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_mk_int64(mty2, 3u64);
    let x·2: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern4: crate::cbordetver::cbor_det_view = x·2;
    let mg0: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern4
        {
            crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
              {
                  let res2: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                      crate::cbordetver::cbor_det_map_get(m3, c12);
                  res2
              },
            _ => panic!("Incomplete pattern matching")
        };
    let res2: crate::cbordetveraux::impl_map_group_result =
        match mg0
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
    let res3: crate::cbordetveraux::impl_map_group_result = res2;
    let test10: crate::cbordetveraux::impl_map_group_result = res3;
    let _bind_c0: option__COSE_Format_evercddl_bstr_pretty =
        if crate::cbordetveraux::uu___is_MGOK(test10)
        {
            let mty3: crate::cbordetver::cbor_det_int_kind =
                if
                crate::cbordetveraux::cbor_major_type_neg_int64
                ==
                crate::cbordetveraux::cbor_major_type_uint64
                { crate::cbordetver::cbor_det_int_kind::UInt64 }
                else
                { crate::cbordetver::cbor_det_int_kind::NegInt64 };
            let c13: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_mk_int64(mty3, 3u64);
            let x·3: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern5: crate::cbordetver::cbor_det_view = x·3;
            let ow1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                match _letpattern5
                {
                    crate::cbordetver::cbor_det_view::Map { _0: m3 } =>
                      {
                          let res4: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                              crate::cbordetver::cbor_det_map_get(m3, c13);
                          res4
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            let _letpattern6: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow1;
            let res4: &[u8] =
                match _letpattern6
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      {
                          let res4: &[u8] = parse_bstr(w);
                          res4
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            let w11: &[u8] = res4;
            option__COSE_Format_evercddl_bstr_pretty::Some { v: w11 }
        }
        else
        { option__COSE_Format_evercddl_bstr_pretty::None };
    let w21: option__COSE_Format_evercddl_bstr_pretty = _bind_c0;
    let
    w11:
    ((((), evercddl_label), option__COSE_Format_evercddl_bstr_pretty),
    option__COSE_Format_evercddl_bstr_pretty)
    =
        (w10,w21);
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern5: crate::cbordetver::cbor_det_view = v1;
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
        match _letpattern5
        {
            crate::cbordetver::cbor_det_view::Map { _0: a } =>
              {
                  let
                  res4: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                  =
                      crate::cbordetver::cbor_det_map_iterator_start(a);
                  res4
              },
            _ => panic!("Incomplete pattern matching")
        };
    let
    rres:
    map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
    =
        map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
        {
            cddl_map_iterator_contents: i,
            cddl_map_iterator_impl_validate1: aux_env25_validate_2,
            cddl_map_iterator_impl_parse1: aux_env25_parse_2,
            cddl_map_iterator_impl_validate_ex: aux_env39_validate_1,
            cddl_map_iterator_impl_validate2: aux_env25_validate_4,
            cddl_map_iterator_impl_parse2: aux_env25_parse_4
        };
    let
    w22:
    either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty
    =
        either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty::Inr
        { v: rres };
    let
    res10:
    (((((), evercddl_label), option__COSE_Format_evercddl_bstr_pretty),
    option__COSE_Format_evercddl_bstr_pretty),
    either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty)
    =
        (w11,w22);
    let res20: evercddl_COSE_Key_OKP_pretty = evercddl_COSE_Key_OKP_pretty_right(res10);
    res20
}

/**
Serializer for evercddl_COSE_Key_OKP
*/
pub fn
serialize_COSE_Key_OKP(c: evercddl_COSE_Key_OKP_pretty, out: &mut [u8]) ->
    usize
{
    let
    c·:
    (((((), evercddl_label), option__COSE_Format_evercddl_bstr_pretty),
    option__COSE_Format_evercddl_bstr_pretty),
    either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty)
    =
        evercddl_COSE_Key_OKP_pretty_left(c);
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let
    _letpattern:
    (((((), evercddl_label), option__COSE_Format_evercddl_bstr_pretty),
    option__COSE_Format_evercddl_bstr_pretty),
    either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty)
    =
        c·;
    let res: bool =
        {
            let
            c1:
            ((((), evercddl_label), option__COSE_Format_evercddl_bstr_pretty),
            option__COSE_Format_evercddl_bstr_pretty)
            =
                _letpattern.0;
            let
            c2:
            either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty
            =
                _letpattern.1;
            let
            _letpattern1:
            ((((), evercddl_label), option__COSE_Format_evercddl_bstr_pretty),
            option__COSE_Format_evercddl_bstr_pretty)
            =
                c1;
            let res1: bool =
                {
                    let c11: (((), evercddl_label), option__COSE_Format_evercddl_bstr_pretty) =
                        _letpattern1.0;
                    let c21: option__COSE_Format_evercddl_bstr_pretty = _letpattern1.1;
                    let
                    _letpattern2: (((), evercddl_label), option__COSE_Format_evercddl_bstr_pretty)
                    =
                        c11;
                    let res1: bool =
                        {
                            let c12: ((), evercddl_label) = _letpattern2.0;
                            let c22: option__COSE_Format_evercddl_bstr_pretty = _letpattern2.1;
                            let _letpattern3: ((), evercddl_label) = c12;
                            let res1: bool =
                                {
                                    _letpattern3.0;
                                    let c23: evercddl_label = _letpattern3.1;
                                    let count: u64 = (&pcount)[0];
                                    let res1: bool =
                                        if count < 18446744073709551615u64
                                        {
                                            let size0: usize = (&psize)[0];
                                            let _letpattern4: (&mut [u8], &mut [u8]) =
                                                out.split_at_mut(size0);
                                            let _out0: &[u8] = _letpattern4.0;
                                            let out1: &mut [u8] = _letpattern4.1;
                                            let mty: crate::cbordetver::cbor_det_int_kind =
                                                crate::cbordetver::cbor_det_int_kind::UInt64;
                                            let c3: crate::cbordetveraux::cbor_raw =
                                                crate::cbordetver::cbor_det_mk_int64(mty, 1u64);
                                            let res: crate::cbordetver::option__size_t =
                                                crate::cbordetver::cbor_det_serialize(c3, out1);
                                            let res0: usize =
                                                match res
                                                {
                                                    crate::cbordetver::option__size_t::None =>
                                                      0usize,
                                                    crate::cbordetver::option__size_t::Some
                                                    { v: r }
                                                    => r,
                                                    _ => panic!("Incomplete pattern matching")
                                                };
                                            let res1: usize = res0;
                                            if res1 > 0usize
                                            {
                                                let size1: usize = size0.wrapping_add(res1);
                                                let _letpattern5: (&mut [u8], &mut [u8]) =
                                                    out.split_at_mut(size1);
                                                let _out01: &[u8] = _letpattern5.0;
                                                let out2: &mut [u8] = _letpattern5.1;
                                                let mty0: crate::cbordetver::cbor_det_int_kind =
                                                    crate::cbordetver::cbor_det_int_kind::UInt64;
                                                let c30: crate::cbordetveraux::cbor_raw =
                                                    crate::cbordetver::cbor_det_mk_int64(mty0, 1u64);
                                                let res2: crate::cbordetver::option__size_t =
                                                    crate::cbordetver::cbor_det_serialize(c30, out2);
                                                let res3: usize =
                                                    match res2
                                                    {
                                                        crate::cbordetver::option__size_t::None =>
                                                          0usize,
                                                        crate::cbordetver::option__size_t::Some
                                                        { v: r }
                                                        => r,
                                                        _ => panic!("Incomplete pattern matching")
                                                    };
                                                let res20: usize = res3;
                                                if res20 > 0usize
                                                {
                                                    let size2: usize = size1.wrapping_add(res20);
                                                    let _letpattern6: (&mut [u8], &mut [u8]) =
                                                        out.split_at_mut(size2);
                                                    let out012: &mut [u8] = _letpattern6.0;
                                                    let res4: bool =
                                                        crate::cbordetver::cbor_det_serialize_map_insert(
                                                            out012,
                                                            size0,
                                                            size1
                                                        );
                                                    if res4
                                                    {
                                                        (&mut psize)[0] = size2;
                                                        (&mut pcount)[0] = count.wrapping_add(1u64);
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
                                        let count0: u64 = (&pcount)[0];
                                        let res2: bool =
                                            if count0 < 18446744073709551615u64
                                            {
                                                let size0: usize = (&psize)[0];
                                                let _letpattern4: (&mut [u8], &mut [u8]) =
                                                    out.split_at_mut(size0);
                                                let _out0: &[u8] = _letpattern4.0;
                                                let out1: &mut [u8] = _letpattern4.1;
                                                let mty: crate::cbordetver::cbor_det_int_kind =
                                                    if
                                                    crate::cbordetveraux::cbor_major_type_neg_int64
                                                    ==
                                                    crate::cbordetveraux::cbor_major_type_uint64
                                                    { crate::cbordetver::cbor_det_int_kind::UInt64 }
                                                    else
                                                    {
                                                        crate::cbordetver::cbor_det_int_kind::NegInt64
                                                    };
                                                let c3: crate::cbordetveraux::cbor_raw =
                                                    crate::cbordetver::cbor_det_mk_int64(mty, 0u64);
                                                let res: crate::cbordetver::option__size_t =
                                                    crate::cbordetver::cbor_det_serialize(c3, out1);
                                                let res0: usize =
                                                    match res
                                                    {
                                                        crate::cbordetver::option__size_t::None =>
                                                          0usize,
                                                        crate::cbordetver::option__size_t::Some
                                                        { v: r }
                                                        => r,
                                                        _ => panic!("Incomplete pattern matching")
                                                    };
                                                let res11: usize = res0;
                                                if res11 > 0usize
                                                {
                                                    let size1: usize = size0.wrapping_add(res11);
                                                    let _letpattern5: (&mut [u8], &mut [u8]) =
                                                        out.split_at_mut(size1);
                                                    let _out01: &[u8] = _letpattern5.0;
                                                    let out2: &mut [u8] = _letpattern5.1;
                                                    let res2: usize =
                                                        match c23
                                                        {
                                                            evercddl_label::Inl { v: c14 } =>
                                                              {
                                                                  let res2: usize =
                                                                      serialize_int(c14, out2);
                                                                  res2
                                                              },
                                                            evercddl_label::Inr { v: c24 } =>
                                                              {
                                                                  let res2: usize =
                                                                      serialize_tstr(c24, out2);
                                                                  res2
                                                              },
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        };
                                                    if res2 > 0usize
                                                    {
                                                        let size2: usize = size1.wrapping_add(res2);
                                                        let _letpattern6: (&mut [u8], &mut [u8]) =
                                                            out.split_at_mut(size2);
                                                        let out012: &mut [u8] = _letpattern6.0;
                                                        let res3: bool =
                                                            crate::cbordetver::cbor_det_serialize_map_insert(
                                                                out012,
                                                                size0,
                                                                size1
                                                            );
                                                        if res3
                                                        {
                                                            (&mut psize)[0] = size2;
                                                            (&mut pcount)[0] =
                                                                count0.wrapping_add(1u64);
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
                                        res2
                                    }
                                    else
                                    { false }
                                };
                            if res1
                            {
                                let res2: bool =
                                    match c22
                                    {
                                        option__COSE_Format_evercddl_bstr_pretty::Some { v: c13 } =>
                                          {
                                              let count: u64 = (&pcount)[0];
                                              let res: bool =
                                                  if count < 18446744073709551615u64
                                                  {
                                                      let size0: usize = (&psize)[0];
                                                      let _letpattern30: (&mut [u8], &mut [u8]) =
                                                          out.split_at_mut(size0);
                                                      let _out0: &[u8] = _letpattern30.0;
                                                      let out1: &mut [u8] = _letpattern30.1;
                                                      let
                                                      mty: crate::cbordetver::cbor_det_int_kind
                                                      =
                                                          if
                                                          crate::cbordetveraux::cbor_major_type_neg_int64
                                                          ==
                                                          crate::cbordetveraux::cbor_major_type_uint64
                                                          {
                                                              crate::cbordetver::cbor_det_int_kind::UInt64
                                                          }
                                                          else
                                                          {
                                                              crate::cbordetver::cbor_det_int_kind::NegInt64
                                                          };
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
                                                      let res0: usize =
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
                                                      let res11: usize = res0;
                                                      if res11 > 0usize
                                                      {
                                                          let size1: usize =
                                                              size0.wrapping_add(res11);
                                                          let _letpattern4: (&mut [u8], &mut [u8]) =
                                                              out.split_at_mut(size1);
                                                          let _out01: &[u8] = _letpattern4.0;
                                                          let out2: &mut [u8] = _letpattern4.1;
                                                          let res2: usize =
                                                              serialize_bstr(c13, out2);
                                                          if res2 > 0usize
                                                          {
                                                              let size2: usize =
                                                                  size1.wrapping_add(res2);
                                                              let
                                                              _letpattern5: (&mut [u8], &mut [u8])
                                                              =
                                                                  out.split_at_mut(size2);
                                                              let out012: &mut [u8] =
                                                                  _letpattern5.0;
                                                              let res3: bool =
                                                                  crate::cbordetver::cbor_det_serialize_map_insert(
                                                                      out012,
                                                                      size0,
                                                                      size1
                                                                  );
                                                              if res3
                                                              {
                                                                  (&mut psize)[0] = size2;
                                                                  (&mut pcount)[0] =
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
                                              res
                                          },
                                        option__COSE_Format_evercddl_bstr_pretty::None => true,
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                res2
                            }
                            else
                            { false }
                        };
                    if res1
                    {
                        let res2: bool =
                            match c21
                            {
                                option__COSE_Format_evercddl_bstr_pretty::Some { v: c12 } =>
                                  {
                                      let count: u64 = (&pcount)[0];
                                      let res: bool =
                                          if count < 18446744073709551615u64
                                          {
                                              let size0: usize = (&psize)[0];
                                              let _letpattern20: (&mut [u8], &mut [u8]) =
                                                  out.split_at_mut(size0);
                                              let _out0: &[u8] = _letpattern20.0;
                                              let out1: &mut [u8] = _letpattern20.1;
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
                                              let res0: usize =
                                                  match res
                                                  {
                                                      crate::cbordetver::option__size_t::None =>
                                                        0usize,
                                                      crate::cbordetver::option__size_t::Some
                                                      { v: r }
                                                      => r,
                                                      _ => panic!("Incomplete pattern matching")
                                                  };
                                              let res11: usize = res0;
                                              if res11 > 0usize
                                              {
                                                  let size1: usize = size0.wrapping_add(res11);
                                                  let _letpattern3: (&mut [u8], &mut [u8]) =
                                                      out.split_at_mut(size1);
                                                  let _out01: &[u8] = _letpattern3.0;
                                                  let out2: &mut [u8] = _letpattern3.1;
                                                  let res2: usize = serialize_bstr(c12, out2);
                                                  if res2 > 0usize
                                                  {
                                                      let size2: usize = size1.wrapping_add(res2);
                                                      let _letpattern4: (&mut [u8], &mut [u8]) =
                                                          out.split_at_mut(size2);
                                                      let out012: &mut [u8] = _letpattern4.0;
                                                      let res3: bool =
                                                          crate::cbordetver::cbor_det_serialize_map_insert(
                                                              out012,
                                                              size0,
                                                              size1
                                                          );
                                                      if res3
                                                      {
                                                          (&mut psize)[0] = size2;
                                                          (&mut pcount)[0] =
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
                                      res
                                  },
                                option__COSE_Format_evercddl_bstr_pretty::None => true,
                                _ => panic!("Incomplete pattern matching")
                            };
                        res2
                    }
                    else
                    { false }
                };
            if res1
            {
                let res2: bool =
                    match c2
                    {
                        either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty::Inl
                        { v: c11 }
                        =>
                          {
                              let i: &[(evercddl_label_pretty, crate::cbordetveraux::cbor_raw)] =
                                  c11;
                              let
                              pi: [&[(evercddl_label_pretty, crate::cbordetveraux::cbor_raw)]; 1]
                              =
                                  [i; 1usize];
                              crate::lowstar::ignore::ignore::<&[&[(evercddl_label_pretty,
                              crate::cbordetveraux::cbor_raw)]]>(&pi);
                              let
                              mut
                              pc:
                              [&[(evercddl_label_pretty, crate::cbordetveraux::cbor_raw)]; 1]
                              =
                                  [i; 1usize];
                              let mut pres: [bool; 1] = [true; 1usize];
                              let res: bool = (&pres)[0];
                              let mut cond: bool =
                                  if res
                                  {
                                      let
                                      c3: &[(evercddl_label_pretty, crate::cbordetveraux::cbor_raw)]
                                      =
                                          (&pc)[0];
                                      let em: bool = c3.len() == 0usize;
                                      ! em
                                  }
                                  else
                                  { false };
                              while
                              cond
                              {
                                  let count: u64 = (&pcount)[0];
                                  if count == 18446744073709551615u64
                                  { (&mut pres)[0] = false }
                                  else
                                  {
                                      let count·: u64 = count.wrapping_add(1u64);
                                      let
                                      i1: &[(evercddl_label_pretty, crate::cbordetveraux::cbor_raw)]
                                      =
                                          (&pc)[0];
                                      let
                                      res0: (evercddl_label_pretty, crate::cbordetveraux::cbor_raw)
                                      =
                                          i1[0usize];
                                      let
                                      _letpattern10:
                                      (&[(evercddl_label_pretty, crate::cbordetveraux::cbor_raw)],
                                      &[(evercddl_label_pretty, crate::cbordetveraux::cbor_raw)])
                                      =
                                          i1.split_at(1usize);
                                      let
                                      _letpattern11:
                                      (evercddl_label_pretty, crate::cbordetveraux::cbor_raw)
                                      =
                                          {
                                              let
                                              _il:
                                              &[(evercddl_label_pretty,
                                              crate::cbordetveraux::cbor_raw)]
                                              =
                                                  _letpattern10.0;
                                              let
                                              ir:
                                              &[(evercddl_label_pretty,
                                              crate::cbordetveraux::cbor_raw)]
                                              =
                                                  _letpattern10.1;
                                              let
                                              i·:
                                              &[(evercddl_label_pretty,
                                              crate::cbordetveraux::cbor_raw)]
                                              =
                                                  ir;
                                              (&mut pc)[0] = i·;
                                              res0
                                          };
                                      let ck: evercddl_label_pretty = _letpattern11.0;
                                      let cv: crate::cbordetveraux::cbor_raw = _letpattern11.1;
                                      let size0: usize = (&psize)[0];
                                      let _letpattern2: (&mut [u8], &mut [u8]) =
                                          out.split_at_mut(size0);
                                      let _outl1: &[u8] = _letpattern2.0;
                                      let out1: &mut [u8] = _letpattern2.1;
                                      let sz1: usize = aux_env25_serialize_2(ck, out1);
                                      if sz1 == 0usize
                                      { (&mut pres)[0] = false }
                                      else
                                      {
                                          let
                                          _letpattern3:
                                          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                          =
                                              crate::cbordetver::cbor_det_parse(out1);
                                          match _letpattern3
                                          {
                                              crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                              { v: oo }
                                              =>
                                                {
                                                    let
                                                    _letpattern4:
                                                    (crate::cbordetveraux::cbor_raw, &[u8])
                                                    =
                                                        oo;
                                                    let o: crate::cbordetveraux::cbor_raw =
                                                        _letpattern4.0;
                                                    let _orem: &[u8] = _letpattern4.1;
                                                    let is_except: bool = aux_env39_validate_1(o);
                                                    if is_except
                                                    { (&mut pres)[0] = false }
                                                    else
                                                    {
                                                        let _letpattern5: (&mut [u8], &mut [u8]) =
                                                            out1.split_at_mut(sz1);
                                                        let _outl2: &[u8] = _letpattern5.0;
                                                        let out2: &mut [u8] = _letpattern5.1;
                                                        let sz2: usize =
                                                            aux_env25_serialize_4(cv, out2);
                                                        if sz2 == 0usize
                                                        { (&mut pres)[0] = false }
                                                        else
                                                        {
                                                            let size1: usize =
                                                                size0.wrapping_add(sz1);
                                                            let size2: usize =
                                                                size1.wrapping_add(sz2);
                                                            let
                                                            _letpattern6: (&mut [u8], &mut [u8])
                                                            =
                                                                out.split_at_mut(size2);
                                                            let
                                                            _letpattern60: (&mut [u8], &mut [u8])
                                                            =
                                                                {
                                                                    let s1: &mut [u8] =
                                                                        _letpattern6.0;
                                                                    let s2: &mut [u8] =
                                                                        _letpattern6.1;
                                                                    (s1,s2)
                                                                };
                                                            let outl: &mut [u8] = _letpattern60.0;
                                                            let _outr: &[u8] = _letpattern60.1;
                                                            let inserted: bool =
                                                                crate::cbordetver::cbor_det_serialize_map_insert(
                                                                    outl,
                                                                    size0,
                                                                    size1
                                                                );
                                                            if ! inserted
                                                            { (&mut pres)[0] = false }
                                                            else
                                                            {
                                                                (&mut pcount)[0] = count·;
                                                                (&mut psize)[0] = size2
                                                            }
                                                        }
                                                    }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          }
                                      }
                                  };
                                  let res0: bool = (&pres)[0];
                                  let ite: bool =
                                      if res0
                                      {
                                          let
                                          c3:
                                          &[(evercddl_label_pretty, crate::cbordetveraux::cbor_raw)]
                                          =
                                              (&pc)[0];
                                          let em: bool = c3.len() == 0usize;
                                          ! em
                                      }
                                      else
                                      { false };
                                  cond = ite
                              };
                              let res0: bool = (&pres)[0];
                              let res2: bool = res0;
                              res2
                          },
                        either__CDDL_Pulse_Types_slice··COSE_Format_aux_env25_type_2_pretty···COSE_Format_aux_env25_type_4_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env25_type_2_pretty·COSE_Format_aux_env25_type_4_pretty::Inr
                        { v: c21 }
                        =>
                          {
                              let
                              mut
                              pc:
                              [map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty;
                              1]
                              =
                                  [c21; 1usize];
                              let mut pres: [bool; 1] = [true; 1usize];
                              let res: bool = (&pres)[0];
                              let mut cond: bool =
                                  if res
                                  {
                                      let
                                      c3:
                                      map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
                                      =
                                          (&pc)[0];
                                      let
                                      mut
                                      pj:
                                      [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry;
                                      1]
                                      =
                                          [c3.cddl_map_iterator_contents; 1usize];
                                      let mut pres1: [bool; 1] = [true; 1usize];
                                      let res2: bool = (&pres1)[0];
                                      let mut cond: bool =
                                          if res2
                                          {
                                              let
                                              j:
                                              crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                              =
                                                  (&pj)[0];
                                              let test: bool =
                                                  crate::cbordetver::cbor_det_map_iterator_is_empty(
                                                      j
                                                  );
                                              ! test
                                          }
                                          else
                                          { false };
                                      while
                                      cond
                                      {
                                          let elt: crate::cbordetveraux::cbor_map_entry =
                                              crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
                                          let elt_key: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(elt);
                                          let test_key: bool =
                                              (c3.cddl_map_iterator_impl_validate1)(elt_key);
                                          if ! ! test_key
                                          {
                                              let test_ex: bool =
                                                  (c3.cddl_map_iterator_impl_validate_ex)(elt_key);
                                              if ! test_ex
                                              {
                                                  let elt_value: crate::cbordetveraux::cbor_raw =
                                                      crate::cbordetver::cbor_det_map_entry_value(
                                                          elt
                                                      );
                                                  let test_value: bool =
                                                      (c3.cddl_map_iterator_impl_validate2)(
                                                          elt_value
                                                      );
                                                  (&mut pres1)[0] = ! test_value
                                              }
                                          };
                                          let res20: bool = (&pres1)[0];
                                          let ite: bool =
                                              if res20
                                              {
                                                  let
                                                  j:
                                                  crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                                  =
                                                      (&pj)[0];
                                                  let test: bool =
                                                      crate::cbordetver::cbor_det_map_iterator_is_empty(
                                                          j
                                                      );
                                                  ! test
                                              }
                                              else
                                              { false };
                                          cond = ite
                                      };
                                      let em: bool = (&pres1)[0];
                                      ! em
                                  }
                                  else
                                  { false };
                              while
                              cond
                              {
                                  let count: u64 = (&pcount)[0];
                                  if count == 18446744073709551615u64
                                  { (&mut pres)[0] = false }
                                  else
                                  {
                                      let count·: u64 = count.wrapping_add(1u64);
                                      let
                                      i:
                                      map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
                                      =
                                          (&pc)[0];
                                      let
                                      mut
                                      pj:
                                      [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry;
                                      1]
                                      =
                                          [i.cddl_map_iterator_contents; 1usize];
                                      let hd0: crate::cbordetveraux::cbor_map_entry =
                                          crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
                                      let mut phd: [crate::cbordetveraux::cbor_map_entry; 1] =
                                          [hd0; 1usize];
                                      let hd: crate::cbordetveraux::cbor_map_entry = (&phd)[0];
                                      let hd_key: crate::cbordetveraux::cbor_raw =
                                          crate::cbordetver::cbor_det_map_entry_key(hd);
                                      let test_key: bool =
                                          (i.cddl_map_iterator_impl_validate1)(hd_key);
                                      let mut cond0: bool =
                                          if ! test_key
                                          { true }
                                          else
                                          {
                                              let test_ex: bool =
                                                  (i.cddl_map_iterator_impl_validate_ex)(hd_key);
                                              if test_ex
                                              { true }
                                              else
                                              {
                                                  let hd_value: crate::cbordetveraux::cbor_raw =
                                                      crate::cbordetver::cbor_det_map_entry_value(
                                                          hd
                                                      );
                                                  let test_value: bool =
                                                      (i.cddl_map_iterator_impl_validate2)(hd_value);
                                                  ! test_value
                                              }
                                          };
                                      while
                                      cond0
                                      {
                                          let hd1: crate::cbordetveraux::cbor_map_entry =
                                              crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
                                          (&mut phd)[0] = hd1;
                                          let hd2: crate::cbordetveraux::cbor_map_entry = (&phd)[0];
                                          let hd_key0: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(hd2);
                                          let test_key0: bool =
                                              (i.cddl_map_iterator_impl_validate1)(hd_key0);
                                          let ite: bool =
                                              if ! test_key0
                                              { true }
                                              else
                                              {
                                                  let test_ex: bool =
                                                      (i.cddl_map_iterator_impl_validate_ex)(
                                                          hd_key0
                                                      );
                                                  if test_ex
                                                  { true }
                                                  else
                                                  {
                                                      let hd_value: crate::cbordetveraux::cbor_raw =
                                                          crate::cbordetver::cbor_det_map_entry_value(
                                                              hd2
                                                          );
                                                      let test_value: bool =
                                                          (i.cddl_map_iterator_impl_validate2)(
                                                              hd_value
                                                          );
                                                      ! test_value
                                                  }
                                              };
                                          cond0 = ite
                                      };
                                      let hd1: crate::cbordetveraux::cbor_map_entry = (&phd)[0];
                                      let hd_key0: crate::cbordetveraux::cbor_raw =
                                          crate::cbordetver::cbor_det_map_entry_key(hd1);
                                      let hd_key_res: evercddl_label_pretty =
                                          (i.cddl_map_iterator_impl_parse1)(hd_key0);
                                      let hd_value: crate::cbordetveraux::cbor_raw =
                                          crate::cbordetver::cbor_det_map_entry_value(hd1);
                                      let hd_value_res: crate::cbordetveraux::cbor_raw =
                                          (i.cddl_map_iterator_impl_parse2)(hd_value);
                                      let
                                      j:
                                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                      =
                                          (&pj)[0];
                                      let
                                      i·:
                                      map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
                                      =
                                          map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
                                          {
                                              cddl_map_iterator_contents: j,
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
                                      (&mut pc)[0] = i·;
                                      let
                                      _letpattern10:
                                      (evercddl_label_pretty, crate::cbordetveraux::cbor_raw)
                                      =
                                          (hd_key_res,hd_value_res);
                                      let ck: evercddl_label_pretty = _letpattern10.0;
                                      let cv: crate::cbordetveraux::cbor_raw = _letpattern10.1;
                                      let size0: usize = (&psize)[0];
                                      let _letpattern2: (&mut [u8], &mut [u8]) =
                                          out.split_at_mut(size0);
                                      let _outl1: &[u8] = _letpattern2.0;
                                      let out1: &mut [u8] = _letpattern2.1;
                                      let sz1: usize = aux_env25_serialize_2(ck, out1);
                                      if sz1 == 0usize
                                      { (&mut pres)[0] = false }
                                      else
                                      {
                                          let
                                          _letpattern3:
                                          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                          =
                                              crate::cbordetver::cbor_det_parse(out1);
                                          match _letpattern3
                                          {
                                              crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                              { v: oo }
                                              =>
                                                {
                                                    let
                                                    _letpattern4:
                                                    (crate::cbordetveraux::cbor_raw, &[u8])
                                                    =
                                                        oo;
                                                    let o: crate::cbordetveraux::cbor_raw =
                                                        _letpattern4.0;
                                                    let _orem: &[u8] = _letpattern4.1;
                                                    let is_except: bool = aux_env39_validate_1(o);
                                                    if is_except
                                                    { (&mut pres)[0] = false }
                                                    else
                                                    {
                                                        let _letpattern5: (&mut [u8], &mut [u8]) =
                                                            out1.split_at_mut(sz1);
                                                        let _outl2: &[u8] = _letpattern5.0;
                                                        let out2: &mut [u8] = _letpattern5.1;
                                                        let sz2: usize =
                                                            aux_env25_serialize_4(cv, out2);
                                                        if sz2 == 0usize
                                                        { (&mut pres)[0] = false }
                                                        else
                                                        {
                                                            let size1: usize =
                                                                size0.wrapping_add(sz1);
                                                            let size2: usize =
                                                                size1.wrapping_add(sz2);
                                                            let
                                                            _letpattern6: (&mut [u8], &mut [u8])
                                                            =
                                                                out.split_at_mut(size2);
                                                            let
                                                            _letpattern60: (&mut [u8], &mut [u8])
                                                            =
                                                                {
                                                                    let s1: &mut [u8] =
                                                                        _letpattern6.0;
                                                                    let s2: &mut [u8] =
                                                                        _letpattern6.1;
                                                                    (s1,s2)
                                                                };
                                                            let outl: &mut [u8] = _letpattern60.0;
                                                            let _outr: &[u8] = _letpattern60.1;
                                                            let inserted: bool =
                                                                crate::cbordetver::cbor_det_serialize_map_insert(
                                                                    outl,
                                                                    size0,
                                                                    size1
                                                                );
                                                            if ! inserted
                                                            { (&mut pres)[0] = false }
                                                            else
                                                            {
                                                                (&mut pcount)[0] = count·;
                                                                (&mut psize)[0] = size2
                                                            }
                                                        }
                                                    }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          }
                                      }
                                  };
                                  let res0: bool = (&pres)[0];
                                  let ite: bool =
                                      if res0
                                      {
                                          let
                                          c3:
                                          map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_aux_env25_type_2_pretty_COSE_Format_aux_env25_type_4_pretty
                                          =
                                              (&pc)[0];
                                          let
                                          mut
                                          pj:
                                          [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry;
                                          1]
                                          =
                                              [c3.cddl_map_iterator_contents; 1usize];
                                          let mut pres1: [bool; 1] = [true; 1usize];
                                          let res2: bool = (&pres1)[0];
                                          let mut cond0: bool =
                                              if res2
                                              {
                                                  let
                                                  j:
                                                  crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                                  =
                                                      (&pj)[0];
                                                  let test: bool =
                                                      crate::cbordetver::cbor_det_map_iterator_is_empty(
                                                          j
                                                      );
                                                  ! test
                                              }
                                              else
                                              { false };
                                          while
                                          cond0
                                          {
                                              let elt: crate::cbordetveraux::cbor_map_entry =
                                                  crate::cbordetver::cbor_det_map_iterator_next(
                                                      &mut pj
                                                  );
                                              let elt_key: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_key(elt);
                                              let test_key: bool =
                                                  (c3.cddl_map_iterator_impl_validate1)(elt_key);
                                              if ! ! test_key
                                              {
                                                  let test_ex: bool =
                                                      (c3.cddl_map_iterator_impl_validate_ex)(
                                                          elt_key
                                                      );
                                                  if ! test_ex
                                                  {
                                                      let
                                                      elt_value: crate::cbordetveraux::cbor_raw
                                                      =
                                                          crate::cbordetver::cbor_det_map_entry_value(
                                                              elt
                                                          );
                                                      let test_value: bool =
                                                          (c3.cddl_map_iterator_impl_validate2)(
                                                              elt_value
                                                          );
                                                      (&mut pres1)[0] = ! test_value
                                                  }
                                              };
                                              let res20: bool = (&pres1)[0];
                                              let ite: bool =
                                                  if res20
                                                  {
                                                      let
                                                      j:
                                                      crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                                      =
                                                          (&pj)[0];
                                                      let test: bool =
                                                          crate::cbordetver::cbor_det_map_iterator_is_empty(
                                                              j
                                                          );
                                                      ! test
                                                  }
                                                  else
                                                  { false };
                                              cond0 = ite
                                          };
                                          let em: bool = (&pres1)[0];
                                          ! em
                                      }
                                      else
                                      { false };
                                  cond = ite
                              };
                              let res0: bool = (&pres)[0];
                              res0
                          },
                        _ => panic!("Incomplete pattern matching")
                    };
                res2
            }
            else
            { false }
        };
    let _bind_c: usize =
        if res
        {
            let size: usize = (&psize)[0];
            let count: u64 = (&pcount)[0];
            crate::cbordetver::cbor_det_serialize_map(count, out, size)
        }
        else
        { 0usize };
    let res0: usize = _bind_c;
    res0
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_COSE_Key_OKP_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_COSE_Key_OKP_pretty <'a>, &'a [u8]) }
}

pub fn validate_and_parse_COSE_Key_OKP <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_COSE_Key_OKP_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_COSE_Key_OKP_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_COSE_Key_OKP(rl);
              if test
              {
                  let x: evercddl_COSE_Key_OKP_pretty = parse_COSE_Key_OKP(rl);
                  option__·COSE_Format_evercddl_COSE_Key_OKP_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_COSE_Key_OKP_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_COSE_Key(c: crate::cbordetveraux::cbor_raw) -> bool
{ validate_COSE_Key_OKP(c) }

pub type evercddl_COSE_Key_pretty <'a> = evercddl_COSE_Key_OKP_pretty <'a>;

pub fn uu___is_Mkevercddl_COSE_Key_pretty0(projectee: evercddl_COSE_Key_OKP_pretty) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_COSE_Key_OKP_pretty>(projectee);
    true
}

fn evercddl_COSE_Key_pretty_right <'a>(x1: evercddl_COSE_Key_OKP_pretty <'a>) ->
    evercddl_COSE_Key_OKP_pretty
    <'a>
{ x1 }

fn evercddl_COSE_Key_pretty_left <'a>(x3: evercddl_COSE_Key_OKP_pretty <'a>) ->
    evercddl_COSE_Key_OKP_pretty
    <'a>
{ x3 }

/**
Parser for evercddl_COSE_Key
*/
pub fn
parse_COSE_Key
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_COSE_Key_OKP_pretty
    <'a>
{
    let res1: evercddl_COSE_Key_OKP_pretty = parse_COSE_Key_OKP(c);
    let res2: evercddl_COSE_Key_OKP_pretty = evercddl_COSE_Key_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_COSE_Key
*/
pub fn
serialize_COSE_Key(c: evercddl_COSE_Key_OKP_pretty, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_COSE_Key_OKP_pretty = evercddl_COSE_Key_pretty_left(c);
    let res: usize = serialize_COSE_Key_OKP(c·, out);
    res
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_COSE_Key_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_COSE_Key_OKP_pretty <'a>, &'a [u8]) }
}

pub fn validate_and_parse_COSE_Key <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_COSE_Key_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_COSE_Key_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_COSE_Key(rl);
              if test
              {
                  let x: evercddl_COSE_Key_OKP_pretty = parse_COSE_Key(rl);
                  option__·COSE_Format_evercddl_COSE_Key_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_COSE_Key_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
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
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let tag·: u64 =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 21u64 == tag·
        {
            let v10: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern0: crate::cbordetver::cbor_det_view = v10;
            let c·: crate::cbordetveraux::cbor_raw =
                match _letpattern0
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let res: bool = validate_any(c·);
            res
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_eb64url_pretty <'a> = evercddl_any_pretty <'a>;

pub fn uu___is_Mkevercddl_eb64url_pretty0(projectee: crate::cbordetveraux::cbor_raw) -> bool
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(projectee);
    true
}

fn evercddl_eb64url_pretty_right <'a>(x1: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x1 }

fn evercddl_eb64url_pretty_left <'a>(x3: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x3 }

/**
Parser for evercddl_eb64url
*/
pub fn
parse_eb64url
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let cpl: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let res: crate::cbordetveraux::cbor_raw = parse_any(cpl);
    let res1: crate::cbordetveraux::cbor_raw = res;
    let res2: crate::cbordetveraux::cbor_raw = evercddl_eb64url_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_eb64url
*/
pub fn
serialize_eb64url(c: crate::cbordetveraux::cbor_raw, out: &mut [u8]) ->
    usize
{
    let c·: crate::cbordetveraux::cbor_raw = evercddl_eb64url_pretty_left(c);
    let c·1: (u64, crate::cbordetveraux::cbor_raw) = (21u64,c·);
    let _letpattern: (u64, crate::cbordetveraux::cbor_raw) = c·1;
    let res: usize =
        {
            let ctag: u64 = _letpattern.0;
            let cpayload: crate::cbordetveraux::cbor_raw = _letpattern.1;
            let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
            if tsz == 0usize
            { 0usize }
            else
            {
                let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
                let out2: &mut [u8] = _letpattern1.1;
                let psz: usize = serialize_any(cpayload, out2);
                if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
            }
        };
    let res0: usize = res;
    res0
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_eb64url_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (crate::cbordetveraux::cbor_raw <'a>, &'a [u8]) }
}

pub fn validate_and_parse_eb64url <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_eb64url_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_eb64url_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_eb64url(rl);
              if test
              {
                  let x: crate::cbordetveraux::cbor_raw = parse_eb64url(rl);
                  option__·COSE_Format_evercddl_eb64url_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_eb64url_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
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
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let tag·: u64 =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 22u64 == tag·
        {
            let v10: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern0: crate::cbordetver::cbor_det_view = v10;
            let c·: crate::cbordetveraux::cbor_raw =
                match _letpattern0
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let res: bool = validate_any(c·);
            res
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_eb64legacy_pretty <'a> = evercddl_any_pretty <'a>;

pub fn uu___is_Mkevercddl_eb64legacy_pretty0(projectee: crate::cbordetveraux::cbor_raw) -> bool
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(projectee);
    true
}

fn evercddl_eb64legacy_pretty_right <'a>(x1: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x1 }

fn evercddl_eb64legacy_pretty_left <'a>(x3: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x3 }

/**
Parser for evercddl_eb64legacy
*/
pub fn
parse_eb64legacy
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let cpl: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let res: crate::cbordetveraux::cbor_raw = parse_any(cpl);
    let res1: crate::cbordetveraux::cbor_raw = res;
    let res2: crate::cbordetveraux::cbor_raw = evercddl_eb64legacy_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_eb64legacy
*/
pub fn
serialize_eb64legacy(c: crate::cbordetveraux::cbor_raw, out: &mut [u8]) ->
    usize
{
    let c·: crate::cbordetveraux::cbor_raw = evercddl_eb64legacy_pretty_left(c);
    let c·1: (u64, crate::cbordetveraux::cbor_raw) = (22u64,c·);
    let _letpattern: (u64, crate::cbordetveraux::cbor_raw) = c·1;
    let res: usize =
        {
            let ctag: u64 = _letpattern.0;
            let cpayload: crate::cbordetveraux::cbor_raw = _letpattern.1;
            let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
            if tsz == 0usize
            { 0usize }
            else
            {
                let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
                let out2: &mut [u8] = _letpattern1.1;
                let psz: usize = serialize_any(cpayload, out2);
                if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
            }
        };
    let res0: usize = res;
    res0
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_eb64legacy_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (crate::cbordetveraux::cbor_raw <'a>, &'a [u8]) }
}

pub fn validate_and_parse_eb64legacy <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_eb64legacy_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_eb64legacy_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_eb64legacy(rl);
              if test
              {
                  let x: crate::cbordetveraux::cbor_raw = parse_eb64legacy(rl);
                  option__·COSE_Format_evercddl_eb64legacy_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_eb64legacy_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
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
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let tag·: u64 =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 23u64 == tag·
        {
            let v10: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern0: crate::cbordetver::cbor_det_view = v10;
            let c·: crate::cbordetveraux::cbor_raw =
                match _letpattern0
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let res: bool = validate_any(c·);
            res
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_eb16_pretty <'a> = evercddl_any_pretty <'a>;

pub fn uu___is_Mkevercddl_eb16_pretty0(projectee: crate::cbordetveraux::cbor_raw) -> bool
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(projectee);
    true
}

fn evercddl_eb16_pretty_right <'a>(x1: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x1 }

fn evercddl_eb16_pretty_left <'a>(x3: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x3 }

/**
Parser for evercddl_eb16
*/
pub fn
parse_eb16
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let cpl: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let res: crate::cbordetveraux::cbor_raw = parse_any(cpl);
    let res1: crate::cbordetveraux::cbor_raw = res;
    let res2: crate::cbordetveraux::cbor_raw = evercddl_eb16_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_eb16
*/
pub fn
serialize_eb16(c: crate::cbordetveraux::cbor_raw, out: &mut [u8]) ->
    usize
{
    let c·: crate::cbordetveraux::cbor_raw = evercddl_eb16_pretty_left(c);
    let c·1: (u64, crate::cbordetveraux::cbor_raw) = (23u64,c·);
    let _letpattern: (u64, crate::cbordetveraux::cbor_raw) = c·1;
    let res: usize =
        {
            let ctag: u64 = _letpattern.0;
            let cpayload: crate::cbordetveraux::cbor_raw = _letpattern.1;
            let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
            if tsz == 0usize
            { 0usize }
            else
            {
                let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
                let out2: &mut [u8] = _letpattern1.1;
                let psz: usize = serialize_any(cpayload, out2);
                if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
            }
        };
    let res0: usize = res;
    res0
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_eb16_pretty···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (crate::cbordetveraux::cbor_raw <'a>, &'a [u8]) }
}

pub fn validate_and_parse_eb16 <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_eb16_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_eb16_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_eb16(rl);
              if test
              {
                  let x: crate::cbordetveraux::cbor_raw = parse_eb16(rl);
                  option__·COSE_Format_evercddl_eb16_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_eb16_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_cborany(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let k: u8 = crate::cbordetver::cbor_det_major_type(c);
    if k == crate::cbordetveraux::cbor_major_type_tagged
    {
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let tag·: u64 =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Tagged { tag, .. } => tag,
                _ => panic!("Incomplete pattern matching")
            };
        if 55799u64 == tag·
        {
            let v10: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern0: crate::cbordetver::cbor_det_view = v10;
            let c·: crate::cbordetveraux::cbor_raw =
                match _letpattern0
                {
                    crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
                    _ => panic!("Incomplete pattern matching")
                };
            let res: bool = validate_any(c·);
            res
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_cborany_pretty <'a> = evercddl_any_pretty <'a>;

pub fn uu___is_Mkevercddl_cborany_pretty0(projectee: crate::cbordetveraux::cbor_raw) -> bool
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(projectee);
    true
}

fn evercddl_cborany_pretty_right <'a>(x1: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x1 }

fn evercddl_cborany_pretty_left <'a>(x3: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x3 }

/**
Parser for evercddl_cborany
*/
pub fn
parse_cborany
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let cpl: crate::cbordetveraux::cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Tagged { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let res: crate::cbordetveraux::cbor_raw = parse_any(cpl);
    let res1: crate::cbordetveraux::cbor_raw = res;
    let res2: crate::cbordetveraux::cbor_raw = evercddl_cborany_pretty_right(res1);
    res2
}

/**
Serializer for evercddl_cborany
*/
pub fn
serialize_cborany(c: crate::cbordetveraux::cbor_raw, out: &mut [u8]) ->
    usize
{
    let c·: crate::cbordetveraux::cbor_raw = evercddl_cborany_pretty_left(c);
    let c·1: (u64, crate::cbordetveraux::cbor_raw) = (55799u64,c·);
    let _letpattern: (u64, crate::cbordetveraux::cbor_raw) = c·1;
    let res: usize =
        {
            let ctag: u64 = _letpattern.0;
            let cpayload: crate::cbordetveraux::cbor_raw = _letpattern.1;
            let tsz: usize = crate::cbordetver::cbor_det_serialize_tag(ctag, out);
            if tsz == 0usize
            { 0usize }
            else
            {
                let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(tsz);
                let out2: &mut [u8] = _letpattern1.1;
                let psz: usize = serialize_any(cpayload, out2);
                if psz == 0usize { 0usize } else { tsz.wrapping_add(psz) }
            }
        };
    let res0: usize = res;
    res0
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_cborany_pretty···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (crate::cbordetveraux::cbor_raw <'a>, &'a [u8]) }
}

pub fn validate_and_parse_cborany <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_cborany_pretty···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_cborany_pretty···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_cborany(rl);
              if test
              {
                  let x: crate::cbordetveraux::cbor_raw = parse_cborany(rl);
                  option__·COSE_Format_evercddl_cborany_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_cborany_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}
