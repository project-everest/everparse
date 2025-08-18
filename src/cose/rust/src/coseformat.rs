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

pub type evercddl_bool = bool;

pub fn uu___is_Mkevercddl_bool0(projectee: bool) -> bool
{
    crate::lowstar::ignore::ignore::<bool>(projectee);
    true
}

fn evercddl_bool_right(x1: bool) -> bool { x1 }

fn evercddl_bool_left(x3: bool) -> bool { x3 }

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
    evercddl_bool_right(res1)
}

/**
Serializer for evercddl_bool
*/
pub fn
serialize_bool(c: bool, out: &mut [u8]) ->
    usize
{
    let c·: bool = evercddl_bool_left(c);
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
pub enum option__·COSE_Format_evercddl_bool···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (bool, &'a [u8]) }
}

pub fn validate_and_parse_bool <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_bool···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_bool···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  option__·COSE_Format_evercddl_bool···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_bool···Pulse_Lib_Slice_slice·uint8_t·::None }
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
pub enum evercddl_everparsenomatch
{ Mkevercddl_everparsenomatch0 }

pub fn uu___is_Mkevercddl_everparsenomatch0(projectee: evercddl_everparsenomatch) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_everparsenomatch>(projectee);
    true
}

fn evercddl_everparsenomatch_right() -> evercddl_everparsenomatch
{ evercddl_everparsenomatch::Mkevercddl_everparsenomatch0 }

/**
Parser for evercddl_everparsenomatch
*/
pub fn
parse_everparsenomatch(c: crate::cbordetveraux::cbor_raw) ->
    evercddl_everparsenomatch
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    evercddl_everparsenomatch_right()
}

/**
Serializer for evercddl_everparsenomatch
*/
pub fn
serialize_everparsenomatch(c: evercddl_everparsenomatch, out: &[u8]) ->
    usize
{
    crate::lowstar::ignore::ignore::<evercddl_everparsenomatch>(c);
    crate::lowstar::ignore::ignore::<&[u8]>(out);
    0usize
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_everparsenomatch···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_everparsenomatch, &'a [u8]) }
}

pub fn validate_and_parse_everparsenomatch <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_everparsenomatch···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_everparsenomatch···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_everparsenomatch = parse_everparsenomatch(rl);
                  option__·COSE_Format_evercddl_everparsenomatch···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_everparsenomatch···Pulse_Lib_Slice_slice·uint8_t·::None
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

pub type evercddl_any_ugly <'a> = crate::cbordetveraux::cbor_raw <'a>;

pub type evercddl_any <'a> = evercddl_any_ugly <'a>;

pub fn uu___is_Mkevercddl_any0(projectee: crate::cbordetveraux::cbor_raw) -> bool
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(projectee);
    true
}

fn evercddl_any_right <'a>(x1: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x1 }

fn evercddl_any_left <'a>(x3: crate::cbordetveraux::cbor_raw <'a>) ->
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
    evercddl_any_right(res1)
}

/**
Serializer for evercddl_any
*/
pub fn
serialize_any(c: crate::cbordetveraux::cbor_raw, out: &mut [u8]) ->
    usize
{
    let c·: crate::cbordetveraux::cbor_raw = evercddl_any_left(c);
    let ser: crate::cbordetver::option__size_t = crate::cbordetver::cbor_det_serialize(c·, out);
    match ser
    {
        crate::cbordetver::option__size_t::None => 0usize,
        crate::cbordetver::option__size_t::Some { v: sz } => sz,
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_any···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (crate::cbordetveraux::cbor_raw <'a>, &'a [u8]) }
}

pub fn validate_and_parse_any <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_any···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_any···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  option__·COSE_Format_evercddl_any···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_any···Pulse_Lib_Slice_slice·uint8_t·::None }
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

#[derive(PartialEq, Clone, Copy)] pub enum evercddl_undefined { Mkevercddl_undefined0 }

pub fn uu___is_Mkevercddl_undefined0(projectee: evercddl_undefined) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_undefined>(projectee);
    true
}

fn evercddl_undefined_right() -> evercddl_undefined
{ evercddl_undefined::Mkevercddl_undefined0 }

/**
Parser for evercddl_undefined
*/
pub fn
parse_undefined(c: crate::cbordetveraux::cbor_raw) ->
    evercddl_undefined
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    evercddl_undefined_right()
}

/**
Serializer for evercddl_undefined
*/
pub fn
serialize_undefined(c: evercddl_undefined, out: &mut [u8]) ->
    usize
{
    crate::lowstar::ignore::ignore::<evercddl_undefined>(c);
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

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_undefined···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_undefined, &'a [u8]) }
}

pub fn validate_and_parse_undefined <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_undefined···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_undefined···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_undefined = parse_undefined(rl);
                  option__·COSE_Format_evercddl_undefined···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_undefined···Pulse_Lib_Slice_slice·uint8_t·::None
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

#[derive(PartialEq, Clone, Copy)] pub enum evercddl_nil { Mkevercddl_nil0 }

pub fn uu___is_Mkevercddl_nil0(projectee: evercddl_nil) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_nil>(projectee);
    true
}

fn evercddl_nil_right() -> evercddl_nil { evercddl_nil::Mkevercddl_nil0 }

/**
Parser for evercddl_nil
*/
pub fn
parse_nil(c: crate::cbordetveraux::cbor_raw) ->
    evercddl_nil
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    evercddl_nil_right()
}

/**
Serializer for evercddl_nil
*/
pub fn
serialize_nil(c: evercddl_nil, out: &mut [u8]) ->
    usize
{
    crate::lowstar::ignore::ignore::<evercddl_nil>(c);
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

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_nil···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_nil, &'a [u8]) }
}

pub fn validate_and_parse_nil <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_nil···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_nil···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_nil = parse_nil(rl);
                  option__·COSE_Format_evercddl_nil···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_nil···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_null(c: crate::cbordetveraux::cbor_raw) -> bool { validate_nil(c) }

pub type evercddl_null = evercddl_nil;

pub fn uu___is_Mkevercddl_null0(projectee: evercddl_nil) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_nil>(projectee);
    true
}

fn evercddl_null_right(x1: evercddl_nil) -> evercddl_nil { x1 }

fn evercddl_null_left(x3: evercddl_nil) -> evercddl_nil { x3 }

/**
Parser for evercddl_null
*/
pub fn
parse_null(c: crate::cbordetveraux::cbor_raw) ->
    evercddl_nil
{
    let res1: evercddl_nil = parse_nil(c);
    evercddl_null_right(res1)
}

/**
Serializer for evercddl_null
*/
pub fn
serialize_null(c: evercddl_nil, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_nil = evercddl_null_left(c);
    serialize_nil(c·, out)
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_null···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_nil, &'a [u8]) }
}

pub fn validate_and_parse_null <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_null···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_null···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_nil = parse_null(rl);
                  option__·COSE_Format_evercddl_null···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_null···Pulse_Lib_Slice_slice·uint8_t·::None }
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

#[derive(PartialEq, Clone, Copy)] pub enum evercddl_true { Mkevercddl_true0 }

pub fn uu___is_Mkevercddl_true0(projectee: evercddl_true) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_true>(projectee);
    true
}

fn evercddl_true_right() -> evercddl_true { evercddl_true::Mkevercddl_true0 }

/**
Parser for evercddl_true
*/
pub fn
parse_true(c: crate::cbordetveraux::cbor_raw) ->
    evercddl_true
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    evercddl_true_right()
}

/**
Serializer for evercddl_true
*/
pub fn
serialize_true(c: evercddl_true, out: &mut [u8]) ->
    usize
{
    crate::lowstar::ignore::ignore::<evercddl_true>(c);
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

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_true···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_true, &'a [u8]) }
}

pub fn validate_and_parse_true <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_true···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_true···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_true = parse_true(rl);
                  option__·COSE_Format_evercddl_true···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_true···Pulse_Lib_Slice_slice·uint8_t·::None }
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

#[derive(PartialEq, Clone, Copy)] pub enum evercddl_false { Mkevercddl_false0 }

pub fn uu___is_Mkevercddl_false0(projectee: evercddl_false) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_false>(projectee);
    true
}

fn evercddl_false_right() -> evercddl_false { evercddl_false::Mkevercddl_false0 }

/**
Parser for evercddl_false
*/
pub fn
parse_false(c: crate::cbordetveraux::cbor_raw) ->
    evercddl_false
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    evercddl_false_right()
}

/**
Serializer for evercddl_false
*/
pub fn
serialize_false(c: evercddl_false, out: &mut [u8]) ->
    usize
{
    crate::lowstar::ignore::ignore::<evercddl_false>(c);
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

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_false···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_false, &'a [u8]) }
}

pub fn validate_and_parse_false <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_false···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_false···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_false = parse_false(rl);
                  option__·COSE_Format_evercddl_false···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_false···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_tstr(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    mt == crate::cbordetveraux::cbor_major_type_text_string
}

pub type evercddl_tstr_ugly <'a> = &'a [u8];

pub type evercddl_tstr <'a> = evercddl_tstr_ugly <'a>;

pub fn uu___is_Mkevercddl_tstr0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_tstr_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_tstr_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

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
    evercddl_tstr_right(res1)
}

/**
Serializer for evercddl_tstr
*/
pub fn
serialize_tstr(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_tstr_left(c);
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
pub enum option__·COSE_Format_evercddl_tstr···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_tstr <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_tstr···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_tstr···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  option__·COSE_Format_evercddl_tstr···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_tstr···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_bstr(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    mt == crate::cbordetveraux::cbor_major_type_byte_string
}

pub type evercddl_bstr <'a> = evercddl_tstr_ugly <'a>;

pub fn uu___is_Mkevercddl_bstr0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_bstr_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_bstr_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

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
    evercddl_bstr_right(res1)
}

/**
Serializer for evercddl_bstr
*/
pub fn
serialize_bstr(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_bstr_left(c);
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
pub enum option__·COSE_Format_evercddl_bstr···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_bstr <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_bstr···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_bstr···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  option__·COSE_Format_evercddl_bstr···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_bstr···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_bytes(c: crate::cbordetveraux::cbor_raw) -> bool { validate_bstr(c) }

pub type evercddl_bytes <'a> = evercddl_bstr <'a>;

pub fn uu___is_Mkevercddl_bytes0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_bytes_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_bytes_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

/**
Parser for evercddl_bytes
*/
pub fn
parse_bytes
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let res1: &[u8] = parse_bstr(c);
    evercddl_bytes_right(res1)
}

/**
Serializer for evercddl_bytes
*/
pub fn
serialize_bytes(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_bytes_left(c);
    serialize_bstr(c·, out)
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_bytes···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_bytes <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_bytes···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_bytes···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  option__·COSE_Format_evercddl_bytes···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_bytes···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_text(c: crate::cbordetveraux::cbor_raw) -> bool { validate_tstr(c) }

pub type evercddl_text <'a> = evercddl_tstr <'a>;

pub fn uu___is_Mkevercddl_text0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_text_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_text_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

/**
Parser for evercddl_text
*/
pub fn
parse_text
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let res1: &[u8] = parse_tstr(c);
    evercddl_text_right(res1)
}

/**
Serializer for evercddl_text
*/
pub fn
serialize_text(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_text_left(c);
    serialize_tstr(c·, out)
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_text···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_text <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_text···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_text···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  option__·COSE_Format_evercddl_text···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_text···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_nint(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    mt == crate::cbordetveraux::cbor_major_type_neg_int64
}

pub type evercddl_nint = u64;

pub fn uu___is_Mkevercddl_nint0(projectee: u64) -> bool
{
    crate::lowstar::ignore::ignore::<u64>(projectee);
    true
}

fn evercddl_nint_right(x1: u64) -> u64 { x1 }

fn evercddl_nint_left(x3: u64) -> u64 { x3 }

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
    let res1: u64 = res;
    evercddl_nint_right(res1)
}

/**
Serializer for evercddl_nint
*/
pub fn
serialize_nint(c: u64, out: &mut [u8]) ->
    usize
{
    let c·: u64 = evercddl_nint_left(c);
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
pub enum option__·COSE_Format_evercddl_nint···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (u64, &'a [u8]) }
}

pub fn validate_and_parse_nint <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_nint···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_nint···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  option__·COSE_Format_evercddl_nint···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_nint···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_uint(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    mt == crate::cbordetveraux::cbor_major_type_uint64
}

pub type evercddl_uint = u64;

pub fn uu___is_Mkevercddl_uint0(projectee: u64) -> bool
{
    crate::lowstar::ignore::ignore::<u64>(projectee);
    true
}

fn evercddl_uint_right(x1: u64) -> u64 { x1 }

fn evercddl_uint_left(x3: u64) -> u64 { x3 }

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
    let res1: u64 = res;
    evercddl_uint_right(res1)
}

/**
Serializer for evercddl_uint
*/
pub fn
serialize_uint(c: u64, out: &mut [u8]) ->
    usize
{
    let c·: u64 = evercddl_uint_left(c);
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
pub enum option__·COSE_Format_evercddl_uint···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (u64, &'a [u8]) }
}

pub fn validate_and_parse_uint <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_uint···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_uint···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  option__·COSE_Format_evercddl_uint···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_uint···Pulse_Lib_Slice_slice·uint8_t·::None }
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
pub enum evercddl_int_ugly_tags
{
    Inl,
    Inr
}

#[derive(PartialEq, Clone, Copy)]
enum evercddl_int_ugly
{
    Inl { v: u64 },
    Inr { v: u64 }
}

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

pub fn uu___is_Mkevercddl_int0(projectee: evercddl_int) -> bool
{ match projectee { evercddl_int::Mkevercddl_int0 { .. } => true, _ => false } }

pub fn uu___is_Mkevercddl_int1(projectee: evercddl_int) -> bool
{ match projectee { evercddl_int::Mkevercddl_int1 { .. } => true, _ => false } }

fn evercddl_int_right(x2: evercddl_int_ugly) -> evercddl_int
{
    match x2
    {
        evercddl_int_ugly::Inl { v: x3 } => evercddl_int::Mkevercddl_int0 { _x0: x3 },
        evercddl_int_ugly::Inr { v: x4 } => evercddl_int::Mkevercddl_int1 { _x0: x4 },
        _ => panic!("Incomplete pattern matching")
    }
}

fn evercddl_int_left(x7: evercddl_int) -> evercddl_int_ugly
{
    match x7
    {
        evercddl_int::Mkevercddl_int0 { _x0: x10 } => evercddl_int_ugly::Inl { v: x10 },
        evercddl_int::Mkevercddl_int1 { _x0: x12 } => evercddl_int_ugly::Inr { v: x12 },
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

/**
Serializer for evercddl_int
*/
pub fn
serialize_int(c: evercddl_int, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_int_ugly = evercddl_int_left(c);
    match c·
    {
        evercddl_int_ugly::Inl { v: c1 } => serialize_uint(c1, out),
        evercddl_int_ugly::Inr { v: c2 } => serialize_nint(c2, out),
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
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
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
            validate_any(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_cborany <'a> = evercddl_any <'a>;

pub fn uu___is_Mkevercddl_cborany0(projectee: crate::cbordetveraux::cbor_raw) -> bool
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(projectee);
    true
}

fn evercddl_cborany_right <'a>(x1: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x1 }

fn evercddl_cborany_left <'a>(x3: crate::cbordetveraux::cbor_raw <'a>) ->
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
    let res1: crate::cbordetveraux::cbor_raw = parse_any(cpl);
    evercddl_cborany_right(res1)
}

/**
Serializer for evercddl_cborany
*/
pub fn
serialize_cborany(c: crate::cbordetveraux::cbor_raw, out: &mut [u8]) ->
    usize
{
    let c·: crate::cbordetveraux::cbor_raw = evercddl_cborany_left(c);
    let c·1: (u64, crate::cbordetveraux::cbor_raw) = (55799u64,c·);
    let _letpattern: (u64, crate::cbordetveraux::cbor_raw) = c·1;
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
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_cborany···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (crate::cbordetveraux::cbor_raw <'a>, &'a [u8]) }
}

pub fn validate_and_parse_cborany <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_cborany···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_cborany···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  option__·COSE_Format_evercddl_cborany···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_cborany···Pulse_Lib_Slice_slice·uint8_t·::None }
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
            validate_tstr(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_mimemessage <'a> = evercddl_tstr <'a>;

pub fn uu___is_Mkevercddl_mimemessage0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_mimemessage_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_mimemessage_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

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
    let res1: &[u8] = parse_tstr(cpl);
    evercddl_mimemessage_right(res1)
}

/**
Serializer for evercddl_mimemessage
*/
pub fn
serialize_mimemessage(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_mimemessage_left(c);
    let c·1: (u64, &[u8]) = (36u64,c·);
    let _letpattern: (u64, &[u8]) = c·1;
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
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_mimemessage···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_mimemessage <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_mimemessage···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_mimemessage···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  option__·COSE_Format_evercddl_mimemessage···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_mimemessage···Pulse_Lib_Slice_slice·uint8_t·::None
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
            validate_tstr(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_regexp <'a> = evercddl_tstr <'a>;

pub fn uu___is_Mkevercddl_regexp0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_regexp_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_regexp_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

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
    let res1: &[u8] = parse_tstr(cpl);
    evercddl_regexp_right(res1)
}

/**
Serializer for evercddl_regexp
*/
pub fn
serialize_regexp(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_regexp_left(c);
    let c·1: (u64, &[u8]) = (35u64,c·);
    let _letpattern: (u64, &[u8]) = c·1;
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
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_regexp···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_regexp <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_regexp···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_regexp···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  option__·COSE_Format_evercddl_regexp···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_regexp···Pulse_Lib_Slice_slice·uint8_t·::None }
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
            validate_tstr(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_b64legacy <'a> = evercddl_tstr <'a>;

pub fn uu___is_Mkevercddl_b64legacy0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_b64legacy_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_b64legacy_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

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
    let res1: &[u8] = parse_tstr(cpl);
    evercddl_b64legacy_right(res1)
}

/**
Serializer for evercddl_b64legacy
*/
pub fn
serialize_b64legacy(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_b64legacy_left(c);
    let c·1: (u64, &[u8]) = (34u64,c·);
    let _letpattern: (u64, &[u8]) = c·1;
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
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_b64legacy···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_b64legacy <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_b64legacy···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_b64legacy···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  option__·COSE_Format_evercddl_b64legacy···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_b64legacy···Pulse_Lib_Slice_slice·uint8_t·::None
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
            validate_tstr(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_b64url <'a> = evercddl_tstr <'a>;

pub fn uu___is_Mkevercddl_b64url0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_b64url_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_b64url_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

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
    let res1: &[u8] = parse_tstr(cpl);
    evercddl_b64url_right(res1)
}

/**
Serializer for evercddl_b64url
*/
pub fn
serialize_b64url(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_b64url_left(c);
    let c·1: (u64, &[u8]) = (33u64,c·);
    let _letpattern: (u64, &[u8]) = c·1;
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
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_b64url···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_b64url <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_b64url···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_b64url···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  option__·COSE_Format_evercddl_b64url···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_b64url···Pulse_Lib_Slice_slice·uint8_t·::None }
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
            validate_tstr(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_uri <'a> = evercddl_tstr <'a>;

pub fn uu___is_Mkevercddl_uri0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_uri_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_uri_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

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
    let res1: &[u8] = parse_tstr(cpl);
    evercddl_uri_right(res1)
}

/**
Serializer for evercddl_uri
*/
pub fn
serialize_uri(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_uri_left(c);
    let c·1: (u64, &[u8]) = (32u64,c·);
    let _letpattern: (u64, &[u8]) = c·1;
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
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_uri···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_uri <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_uri···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_uri···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  option__·COSE_Format_evercddl_uri···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_uri···Pulse_Lib_Slice_slice·uint8_t·::None }
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
            validate_bstr(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_encodedcbor <'a> = evercddl_bstr <'a>;

pub fn uu___is_Mkevercddl_encodedcbor0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_encodedcbor_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_encodedcbor_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

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
    let res1: &[u8] = parse_bstr(cpl);
    evercddl_encodedcbor_right(res1)
}

/**
Serializer for evercddl_encodedcbor
*/
pub fn
serialize_encodedcbor(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_encodedcbor_left(c);
    let c·1: (u64, &[u8]) = (24u64,c·);
    let _letpattern: (u64, &[u8]) = c·1;
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
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_encodedcbor···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_encodedcbor <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_encodedcbor···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_encodedcbor···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  option__·COSE_Format_evercddl_encodedcbor···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_encodedcbor···Pulse_Lib_Slice_slice·uint8_t·::None
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
            validate_any(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_eb16 <'a> = evercddl_any <'a>;

pub fn uu___is_Mkevercddl_eb160(projectee: crate::cbordetveraux::cbor_raw) -> bool
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(projectee);
    true
}

fn evercddl_eb16_right <'a>(x1: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x1 }

fn evercddl_eb16_left <'a>(x3: crate::cbordetveraux::cbor_raw <'a>) ->
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
    let res1: crate::cbordetveraux::cbor_raw = parse_any(cpl);
    evercddl_eb16_right(res1)
}

/**
Serializer for evercddl_eb16
*/
pub fn
serialize_eb16(c: crate::cbordetveraux::cbor_raw, out: &mut [u8]) ->
    usize
{
    let c·: crate::cbordetveraux::cbor_raw = evercddl_eb16_left(c);
    let c·1: (u64, crate::cbordetveraux::cbor_raw) = (23u64,c·);
    let _letpattern: (u64, crate::cbordetveraux::cbor_raw) = c·1;
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
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_eb16···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (crate::cbordetveraux::cbor_raw <'a>, &'a [u8]) }
}

pub fn validate_and_parse_eb16 <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_eb16···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_eb16···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  option__·COSE_Format_evercddl_eb16···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_eb16···Pulse_Lib_Slice_slice·uint8_t·::None }
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
            validate_any(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_eb64legacy <'a> = evercddl_any <'a>;

pub fn uu___is_Mkevercddl_eb64legacy0(projectee: crate::cbordetveraux::cbor_raw) -> bool
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(projectee);
    true
}

fn evercddl_eb64legacy_right <'a>(x1: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x1 }

fn evercddl_eb64legacy_left <'a>(x3: crate::cbordetveraux::cbor_raw <'a>) ->
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
    let res1: crate::cbordetveraux::cbor_raw = parse_any(cpl);
    evercddl_eb64legacy_right(res1)
}

/**
Serializer for evercddl_eb64legacy
*/
pub fn
serialize_eb64legacy(c: crate::cbordetveraux::cbor_raw, out: &mut [u8]) ->
    usize
{
    let c·: crate::cbordetveraux::cbor_raw = evercddl_eb64legacy_left(c);
    let c·1: (u64, crate::cbordetveraux::cbor_raw) = (22u64,c·);
    let _letpattern: (u64, crate::cbordetveraux::cbor_raw) = c·1;
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
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_eb64legacy···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (crate::cbordetveraux::cbor_raw <'a>, &'a [u8]) }
}

pub fn validate_and_parse_eb64legacy <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_eb64legacy···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_eb64legacy···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  option__·COSE_Format_evercddl_eb64legacy···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_eb64legacy···Pulse_Lib_Slice_slice·uint8_t·::None
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
            validate_any(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_eb64url <'a> = evercddl_any <'a>;

pub fn uu___is_Mkevercddl_eb64url0(projectee: crate::cbordetveraux::cbor_raw) -> bool
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(projectee);
    true
}

fn evercddl_eb64url_right <'a>(x1: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x1 }

fn evercddl_eb64url_left <'a>(x3: crate::cbordetveraux::cbor_raw <'a>) ->
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
    let res1: crate::cbordetveraux::cbor_raw = parse_any(cpl);
    evercddl_eb64url_right(res1)
}

/**
Serializer for evercddl_eb64url
*/
pub fn
serialize_eb64url(c: crate::cbordetveraux::cbor_raw, out: &mut [u8]) ->
    usize
{
    let c·: crate::cbordetveraux::cbor_raw = evercddl_eb64url_left(c);
    let c·1: (u64, crate::cbordetveraux::cbor_raw) = (21u64,c·);
    let _letpattern: (u64, crate::cbordetveraux::cbor_raw) = c·1;
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
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_eb64url···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (crate::cbordetveraux::cbor_raw <'a>, &'a [u8]) }
}

pub fn validate_and_parse_eb64url <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_eb64url···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_eb64url···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  option__·COSE_Format_evercddl_eb64url···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_eb64url···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_number(c: crate::cbordetveraux::cbor_raw) -> bool { validate_int(c) }

pub type evercddl_number = evercddl_int;

pub fn uu___is_Mkevercddl_number0(projectee: evercddl_int) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_int>(projectee);
    true
}

fn evercddl_number_right(x1: evercddl_int) -> evercddl_int { x1 }

fn evercddl_number_left(x3: evercddl_int) -> evercddl_int { x3 }

/**
Parser for evercddl_number
*/
pub fn
parse_number(c: crate::cbordetveraux::cbor_raw) ->
    evercddl_int
{
    let res1: evercddl_int = parse_int(c);
    evercddl_number_right(res1)
}

/**
Serializer for evercddl_number
*/
pub fn
serialize_number(c: evercddl_int, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_int = evercddl_number_left(c);
    serialize_int(c·, out)
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_number···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_int, &'a [u8]) }
}

pub fn validate_and_parse_number <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_number···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_number···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_number(rl);
              if test
              {
                  let x: evercddl_int = parse_number(rl);
                  option__·COSE_Format_evercddl_number···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_number···Pulse_Lib_Slice_slice·uint8_t·::None }
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
            validate_tstr(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_tdate <'a> = evercddl_tstr <'a>;

pub fn uu___is_Mkevercddl_tdate0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn evercddl_tdate_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn evercddl_tdate_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

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
    let res1: &[u8] = parse_tstr(cpl);
    evercddl_tdate_right(res1)
}

/**
Serializer for evercddl_tdate
*/
pub fn
serialize_tdate(c: &[u8], out: &mut [u8]) ->
    usize
{
    let c·: &[u8] = evercddl_tdate_left(c);
    let c·1: (u64, &[u8]) = (0u64,c·);
    let _letpattern: (u64, &[u8]) = c·1;
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
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_tdate···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_tdate <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_tdate···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_tdate···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  option__·COSE_Format_evercddl_tdate···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_tdate···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_values(c: crate::cbordetveraux::cbor_raw) -> bool { validate_any(c) }

pub type evercddl_values <'a> = evercddl_any <'a>;

pub fn uu___is_Mkevercddl_values0(projectee: crate::cbordetveraux::cbor_raw) -> bool
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(projectee);
    true
}

fn evercddl_values_right <'a>(x1: crate::cbordetveraux::cbor_raw <'a>) ->
    crate::cbordetveraux::cbor_raw
    <'a>
{ x1 }

fn evercddl_values_left <'a>(x3: crate::cbordetveraux::cbor_raw <'a>) ->
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
    evercddl_values_right(res1)
}

/**
Serializer for evercddl_values
*/
pub fn
serialize_values(c: crate::cbordetveraux::cbor_raw, out: &mut [u8]) ->
    usize
{
    let c·: crate::cbordetveraux::cbor_raw = evercddl_values_left(c);
    serialize_any(c·, out)
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_values···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (crate::cbordetveraux::cbor_raw <'a>, &'a [u8]) }
}

pub fn validate_and_parse_values <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_values···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_values···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  option__·COSE_Format_evercddl_values···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_values···Pulse_Lib_Slice_slice·uint8_t·::None }
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
pub enum evercddl_label_ugly <'a>
{
    Inl { v: evercddl_int },
    Inr { v: &'a [u8] }
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

pub fn uu___is_Mkevercddl_label0(projectee: evercddl_label) -> bool
{ match projectee { evercddl_label::Mkevercddl_label0 { .. } => true, _ => false } }

pub fn uu___is_Mkevercddl_label1(projectee: evercddl_label) -> bool
{ match projectee { evercddl_label::Mkevercddl_label1 { .. } => true, _ => false } }

fn evercddl_label_right <'a>(x2: evercddl_label_ugly <'a>) -> evercddl_label <'a>
{
    match x2
    {
        evercddl_label_ugly::Inl { v: x3 } => evercddl_label::Mkevercddl_label0 { _x0: x3 },
        evercddl_label_ugly::Inr { v: x4 } => evercddl_label::Mkevercddl_label1 { _x0: x4 },
        _ => panic!("Incomplete pattern matching")
    }
}

fn evercddl_label_left <'a>(x7: evercddl_label <'a>) -> evercddl_label_ugly <'a>
{
    match x7
    {
        evercddl_label::Mkevercddl_label0 { _x0: x10 } => evercddl_label_ugly::Inl { v: x10 },
        evercddl_label::Mkevercddl_label1 { _x0: x12 } => evercddl_label_ugly::Inr { v: x12 },
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Parser for evercddl_label
*/
pub fn
parse_label
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_label
    <'a>
{
    let test: bool = validate_int(c);
    let res1: evercddl_label_ugly =
        if test
        {
            let res: evercddl_int = parse_int(c);
            evercddl_label_ugly::Inl { v: res }
        }
        else
        {
            let res: &[u8] = parse_tstr(c);
            evercddl_label_ugly::Inr { v: res }
        };
    evercddl_label_right(res1)
}

/**
Serializer for evercddl_label
*/
pub fn
serialize_label(c: evercddl_label, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_label_ugly = evercddl_label_left(c);
    match c·
    {
        evercddl_label_ugly::Inl { v: c1 } => serialize_int(c1, out),
        evercddl_label_ugly::Inr { v: c2 } => serialize_tstr(c2, out),
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_label···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_label <'a>, &'a [u8]) }
}

pub fn validate_and_parse_label <'a>(s: &'a [u8]) ->
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
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_label(rl);
              if test
              {
                  let x: evercddl_label = parse_label(rl);
                  option__·COSE_Format_evercddl_label···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_label···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn aux_env29_map_constraint_1(x: crate::cbordetveraux::cbor_map_entry) -> bool
{
    let k: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
    let mt: u8 = crate::cbordetver::cbor_det_major_type(k);
    let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;
    let testk: bool =
        if is_uint
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(k);
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
    let test: bool =
        if testk
        {
            let v1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_value(x);
            crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(v1);
            true
        }
        else
        { false };
    let test0: bool =
        if test
        { true }
        else
        {
            let k0: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
            let mt0: u8 = crate::cbordetver::cbor_det_major_type(k0);
            let is_uint0: bool = mt0 == crate::cbordetveraux::cbor_major_type_neg_int64;
            let testk0: bool =
                if is_uint0
                {
                    let v1: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(k0);
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
                { false };
            if testk0
            {
                let v1: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_map_entry_value(x);
                crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(v1);
                true
            }
            else
            { false }
        };
    let test1: bool =
        if test0
        { true }
        else
        {
            let k0: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
            let mt0: u8 = crate::cbordetver::cbor_det_major_type(k0);
            let is_uint0: bool = mt0 == crate::cbordetveraux::cbor_major_type_neg_int64;
            let testk0: bool =
                if is_uint0
                {
                    let v1: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(k0);
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
            if testk0
            {
                let v1: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_map_entry_value(x);
                crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(v1);
                true
            }
            else
            { false }
        };
    if test1
    { true }
    else
    {
        let k0: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
        let mt0: u8 = crate::cbordetver::cbor_det_major_type(k0);
        let is_uint0: bool = mt0 == crate::cbordetveraux::cbor_major_type_neg_int64;
        let testk0: bool =
            if is_uint0
            {
                let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(k0);
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
            { false };
        if testk0
        {
            let v1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_value(x);
            crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(v1);
            true
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
                  crate::cbordetver::cbor_det_map_length(a),
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
                  crate::cbordetver::cbor_det_map_get(m1, c1),
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
                                crate::cbordetver::cbor_det_map_get(m2, c10),
                              _ => panic!("Incomplete pattern matching")
                          };
                      match mg0
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
                      }
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
                                crate::cbordetver::cbor_det_map_get(m2, c10),
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res11: crate::cbordetveraux::impl_map_group_result =
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
                                crate::cbordetver::cbor_det_map_get(m2, c10),
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res110: crate::cbordetveraux::impl_map_group_result =
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
                      }
                  },
                crate::cbordetveraux::impl_map_group_result::MGFail =>
                  crate::cbordetveraux::impl_map_group_result::MGFail,
                crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                  crate::cbordetveraux::impl_map_group_result::MGCutFail,
                _ => panic!("Precondition of the function most likely violated")
            };
        let res: crate::cbordetveraux::impl_map_group_result =
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
                          let testk: bool = validate_label(k);
                          let test: bool =
                              if testk
                              {
                                  let v11: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_value(chd);
                                  validate_values(v11)
                              }
                              else
                              { false };
                          let test0: bool =
                              if test
                              {
                                  let k0: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_key(chd);
                                  let mt: u8 = crate::cbordetver::cbor_det_major_type(k0);
                                  let is_uint: bool =
                                      mt == crate::cbordetveraux::cbor_major_type_uint64;
                                  let testk0: bool =
                                      if is_uint
                                      {
                                          let v11: crate::cbordetver::cbor_det_view =
                                              crate::cbordetver::cbor_det_destruct(k0);
                                          let _letpattern2: crate::cbordetver::cbor_det_view = v11;
                                          let i: u64 =
                                              match _letpattern2
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
                                      if testk0
                                      {
                                          let v11: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_value(chd);
                                          crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(
                                              v11
                                          );
                                          true
                                      }
                                      else
                                      { false };
                                  let test10: bool =
                                      if test1
                                      { true }
                                      else
                                      {
                                          let k1: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(chd);
                                          let mt0: u8 = crate::cbordetver::cbor_det_major_type(k1);
                                          let is_uint0: bool =
                                              mt0 == crate::cbordetveraux::cbor_major_type_neg_int64;
                                          let testk1: bool =
                                              if is_uint0
                                              {
                                                  let v11: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(k1);
                                                  let
                                                  _letpattern2: crate::cbordetver::cbor_det_view
                                                  =
                                                      v11;
                                                  let i: u64 =
                                                      match _letpattern2
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
                                          if testk1
                                          {
                                              let v11: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(chd);
                                              crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(
                                                  v11
                                              );
                                              true
                                          }
                                          else
                                          { false }
                                      };
                                  let test11: bool =
                                      if test10
                                      { true }
                                      else
                                      {
                                          let k1: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(chd);
                                          let mt0: u8 = crate::cbordetver::cbor_det_major_type(k1);
                                          let is_uint0: bool =
                                              mt0 == crate::cbordetveraux::cbor_major_type_neg_int64;
                                          let testk1: bool =
                                              if is_uint0
                                              {
                                                  let v11: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(k1);
                                                  let
                                                  _letpattern2: crate::cbordetver::cbor_det_view
                                                  =
                                                      v11;
                                                  let i: u64 =
                                                      match _letpattern2
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
                                          if testk1
                                          {
                                              let v11: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(chd);
                                              crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(
                                                  v11
                                              );
                                              true
                                          }
                                          else
                                          { false }
                                      };
                                  let test12: bool =
                                      if test11
                                      { true }
                                      else
                                      {
                                          let k1: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(chd);
                                          let mt0: u8 = crate::cbordetver::cbor_det_major_type(k1);
                                          let is_uint0: bool =
                                              mt0 == crate::cbordetveraux::cbor_major_type_neg_int64;
                                          let testk1: bool =
                                              if is_uint0
                                              {
                                                  let v11: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(k1);
                                                  let
                                                  _letpattern2: crate::cbordetver::cbor_det_view
                                                  =
                                                      v11;
                                                  let i: u64 =
                                                      match _letpattern2
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
                                          if testk1
                                          {
                                              let v11: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(chd);
                                              crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(
                                                  v11
                                              );
                                              true
                                          }
                                          else
                                          { false }
                                      };
                                  ! test12
                              }
                              else
                              { false };
                          let test1: bool = ! test0;
                          if ! test1
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
pub enum option__COSE_Format_evercddl_bstr <'a>
{
    None,
    Some { v: &'a [u8] }
}

#[derive(PartialEq, Clone, Copy)]
pub struct
map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
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
either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values
<'a>
{
    Inl { v: &'a [(evercddl_label <'a>, crate::cbordetveraux::cbor_raw <'a>)] },
    Inr
    {
        v:
        map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
        <'a>
    }
}

#[derive(PartialEq, Clone, Copy)]
pub struct evercddl_COSE_Key_OKP <'a>
{
    pub intkeyneg1: evercddl_label_ugly <'a>,
    pub intkeyneg2: option__COSE_Format_evercddl_bstr <'a>,
    pub intkeyneg4: option__COSE_Format_evercddl_bstr <'a>,
    pub _x0:
    either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values
    <'a>
}

pub fn uu___is_Mkevercddl_COSE_Key_OKP0(projectee: evercddl_COSE_Key_OKP) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_COSE_Key_OKP>(projectee);
    true
}

fn evercddl_COSE_Key_OKP_right <'a>(
    x5:
    (((((), evercddl_label_ugly <'a>), option__COSE_Format_evercddl_bstr <'a>),
    option__COSE_Format_evercddl_bstr
    <'a>),
    either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values
    <'a>)
) ->
    evercddl_COSE_Key_OKP
    <'a>
{
    match x5
    {
        ((((_x6,x7),x8),x9),x10) =>
          evercddl_COSE_Key_OKP { intkeyneg1: x7, intkeyneg2: x8, intkeyneg4: x9, _x0: x10 }
    }
}

fn evercddl_COSE_Key_OKP_left <'a>(x11: evercddl_COSE_Key_OKP <'a>) ->
    (((((), evercddl_label_ugly <'a>), option__COSE_Format_evercddl_bstr <'a>),
    option__COSE_Format_evercddl_bstr
    <'a>),
    either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values
    <'a>)
{
    let x19: evercddl_label_ugly = x11.intkeyneg1;
    let x20: option__COSE_Format_evercddl_bstr = x11.intkeyneg2;
    let x21: option__COSE_Format_evercddl_bstr = x11.intkeyneg4;
    let
    x22:
    either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values
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
    evercddl_COSE_Key_OKP
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
              crate::cbordetver::cbor_det_map_get(m3, c1),
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
              crate::cbordetver::cbor_det_map_get(m3, c10),
            _ => panic!("Incomplete pattern matching")
        };
    let _letpattern2: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow0;
    let w2: evercddl_label_ugly =
        match _letpattern2
        {
            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
              {
                  let test: bool = validate_int(w);
                  if test
                  {
                      let res: evercddl_int = parse_int(w);
                      evercddl_label_ugly::Inl { v: res }
                  }
                  else
                  {
                      let res: &[u8] = parse_tstr(w);
                      evercddl_label_ugly::Inr { v: res }
                  }
              },
            _ => panic!("Incomplete pattern matching")
        };
    let w1: ((), evercddl_label_ugly) = ((),w2);
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
              crate::cbordetver::cbor_det_map_get(m3, c11),
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
    let w20: option__COSE_Format_evercddl_bstr =
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
                      crate::cbordetver::cbor_det_map_get(m3, c12),
                    _ => panic!("Incomplete pattern matching")
                };
            let _letpattern5: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow1;
            let w11: &[u8] =
                match _letpattern5
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      parse_bstr(w),
                    _ => panic!("Incomplete pattern matching")
                };
            option__COSE_Format_evercddl_bstr::Some { v: w11 }
        }
        else
        { option__COSE_Format_evercddl_bstr::None };
    let w10: (((), evercddl_label_ugly), option__COSE_Format_evercddl_bstr) = (w1,w20);
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
              crate::cbordetver::cbor_det_map_get(m3, c12),
            _ => panic!("Incomplete pattern matching")
        };
    let test10: crate::cbordetveraux::impl_map_group_result =
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
    let w21: option__COSE_Format_evercddl_bstr =
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
                      crate::cbordetver::cbor_det_map_get(m3, c13),
                    _ => panic!("Incomplete pattern matching")
                };
            let _letpattern6: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow1;
            let w11: &[u8] =
                match _letpattern6
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      parse_bstr(w),
                    _ => panic!("Incomplete pattern matching")
                };
            option__COSE_Format_evercddl_bstr::Some { v: w11 }
        }
        else
        { option__COSE_Format_evercddl_bstr::None };
    let
    w11:
    ((((), evercddl_label_ugly), option__COSE_Format_evercddl_bstr),
    option__COSE_Format_evercddl_bstr)
    =
        (w10,w21);
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern5: crate::cbordetver::cbor_det_view = v1;
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
        match _letpattern5
        {
            crate::cbordetver::cbor_det_view::Map { _0: a } =>
              crate::cbordetver::cbor_det_map_iterator_start(a),
            _ => panic!("Incomplete pattern matching")
        };
    let
    rres:
    map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
    =
        map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
        {
            cddl_map_iterator_contents: i,
            cddl_map_iterator_impl_validate1: validate_label,
            cddl_map_iterator_impl_parse1: parse_label,
            cddl_map_iterator_impl_validate_ex: aux_env29_map_constraint_1,
            cddl_map_iterator_impl_validate2: validate_values,
            cddl_map_iterator_impl_parse2: parse_values
        };
    let
    w22:
    either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values
    =
        either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values::Inr
        { v: rres };
    let
    res1:
    (((((), evercddl_label_ugly), option__COSE_Format_evercddl_bstr),
    option__COSE_Format_evercddl_bstr),
    either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values)
    =
        (w11,w22);
    evercddl_COSE_Key_OKP_right(res1)
}

/**
Serializer for evercddl_COSE_Key_OKP
*/
pub fn
serialize_COSE_Key_OKP(c: evercddl_COSE_Key_OKP, out: &mut [u8]) ->
    usize
{
    let
    c·:
    (((((), evercddl_label_ugly), option__COSE_Format_evercddl_bstr),
    option__COSE_Format_evercddl_bstr),
    either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values)
    =
        evercddl_COSE_Key_OKP_left(c);
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let
    _letpattern:
    (((((), evercddl_label_ugly), option__COSE_Format_evercddl_bstr),
    option__COSE_Format_evercddl_bstr),
    either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values)
    =
        c·;
    let res: bool =
        {
            let
            c1:
            ((((), evercddl_label_ugly), option__COSE_Format_evercddl_bstr),
            option__COSE_Format_evercddl_bstr)
            =
                _letpattern.0;
            let
            c2:
            either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values
            =
                _letpattern.1;
            let
            _letpattern1:
            ((((), evercddl_label_ugly), option__COSE_Format_evercddl_bstr),
            option__COSE_Format_evercddl_bstr)
            =
                c1;
            let res1: bool =
                {
                    let c11: (((), evercddl_label_ugly), option__COSE_Format_evercddl_bstr) =
                        _letpattern1.0;
                    let c21: option__COSE_Format_evercddl_bstr = _letpattern1.1;
                    let
                    _letpattern2: (((), evercddl_label_ugly), option__COSE_Format_evercddl_bstr)
                    =
                        c11;
                    let res1: bool =
                        {
                            let c12: ((), evercddl_label_ugly) = _letpattern2.0;
                            let c22: option__COSE_Format_evercddl_bstr = _letpattern2.1;
                            let _letpattern3: ((), evercddl_label_ugly) = c12;
                            let res1: bool =
                                {
                                    _letpattern3.0;
                                    let c23: evercddl_label_ugly = _letpattern3.1;
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
                                                let _letpattern5: (&mut [u8], &mut [u8]) =
                                                    out.split_at_mut(size1);
                                                let _out01: &[u8] = _letpattern5.0;
                                                let out2: &mut [u8] = _letpattern5.1;
                                                let mty0: crate::cbordetver::cbor_det_int_kind =
                                                    crate::cbordetver::cbor_det_int_kind::UInt64;
                                                let c30: crate::cbordetveraux::cbor_raw =
                                                    crate::cbordetver::cbor_det_mk_int64(mty0, 1u64);
                                                let res0: crate::cbordetver::option__size_t =
                                                    crate::cbordetver::cbor_det_serialize(c30, out2);
                                                let res2: usize =
                                                    match res0
                                                    {
                                                        crate::cbordetver::option__size_t::None =>
                                                          0usize,
                                                        crate::cbordetver::option__size_t::Some
                                                        { v: r }
                                                        => r,
                                                        _ => panic!("Incomplete pattern matching")
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
                                                let _letpattern5: (&mut [u8], &mut [u8]) =
                                                    out.split_at_mut(size1);
                                                let _out01: &[u8] = _letpattern5.0;
                                                let out2: &mut [u8] = _letpattern5.1;
                                                let res2: usize =
                                                    match c23
                                                    {
                                                        evercddl_label_ugly::Inl { v: c14 } =>
                                                          serialize_int(c14, out2),
                                                        evercddl_label_ugly::Inr { v: c24 } =>
                                                          serialize_tstr(c24, out2),
                                                        _ => panic!("Incomplete pattern matching")
                                                    };
                                                if res2 > 0usize
                                                {
                                                    let size2: usize = size1.wrapping_add(res2);
                                                    let _letpattern6: (&mut [u8], &mut [u8]) =
                                                        out.split_at_mut(size2);
                                                    let out012: &mut [u8] = _letpattern6.0;
                                                    let res0: bool =
                                                        crate::cbordetver::cbor_det_serialize_map_insert(
                                                            out012,
                                                            size0,
                                                            size1
                                                        );
                                                    if res0
                                                    {
                                                        (&mut psize)[0] = size2;
                                                        (&mut pcount)[0] = count0.wrapping_add(1u64);
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
                                    option__COSE_Format_evercddl_bstr::Some { v: c13 } =>
                                      {
                                          let count: u64 = (&pcount)[0];
                                          if count < 18446744073709551615u64
                                          {
                                              let size0: usize = (&psize)[0];
                                              let _letpattern30: (&mut [u8], &mut [u8]) =
                                                  out.split_at_mut(size0);
                                              let _out0: &[u8] = _letpattern30.0;
                                              let out1: &mut [u8] = _letpattern30.1;
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
                                                  let _letpattern4: (&mut [u8], &mut [u8]) =
                                                      out.split_at_mut(size1);
                                                  let _out01: &[u8] = _letpattern4.0;
                                                  let out2: &mut [u8] = _letpattern4.1;
                                                  let res2: usize = serialize_bstr(c13, out2);
                                                  if res2 > 0usize
                                                  {
                                                      let size2: usize = size1.wrapping_add(res2);
                                                      let _letpattern5: (&mut [u8], &mut [u8]) =
                                                          out.split_at_mut(size2);
                                                      let out012: &mut [u8] = _letpattern5.0;
                                                      let res0: bool =
                                                          crate::cbordetver::cbor_det_serialize_map_insert(
                                                              out012,
                                                              size0,
                                                              size1
                                                          );
                                                      if res0
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
                                          { false }
                                      },
                                    option__COSE_Format_evercddl_bstr::None => true,
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
                            option__COSE_Format_evercddl_bstr::Some { v: c12 } =>
                              {
                                  let count: u64 = (&pcount)[0];
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
                                              let res0: bool =
                                                  crate::cbordetver::cbor_det_serialize_map_insert(
                                                      out012,
                                                      size0,
                                                      size1
                                                  );
                                              if res0
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
                                  { false }
                              },
                            option__COSE_Format_evercddl_bstr::None => true,
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
                    either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values::Inl
                    { v: c11 }
                    =>
                      {
                          let i: &[(evercddl_label, crate::cbordetveraux::cbor_raw)] = c11;
                          let pi: [&[(evercddl_label, crate::cbordetveraux::cbor_raw)]; 1] =
                              [i; 1usize];
                          crate::lowstar::ignore::ignore::<&[&[(evercddl_label,
                          crate::cbordetveraux::cbor_raw)]]>(&pi);
                          let mut pc: [&[(evercddl_label, crate::cbordetveraux::cbor_raw)]; 1] =
                              [i; 1usize];
                          let mut pres: [bool; 1] = [true; 1usize];
                          let res: bool = (&pres)[0];
                          let mut cond: bool =
                              if res
                              {
                                  let c3: &[(evercddl_label, crate::cbordetveraux::cbor_raw)] =
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
                                  let i1: &[(evercddl_label, crate::cbordetveraux::cbor_raw)] =
                                      (&pc)[0];
                                  let res0: (evercddl_label, crate::cbordetveraux::cbor_raw) =
                                      i1[0usize];
                                  let
                                  _letpattern10:
                                  (&[(evercddl_label, crate::cbordetveraux::cbor_raw)],
                                  &[(evercddl_label, crate::cbordetveraux::cbor_raw)])
                                  =
                                      i1.split_at(1usize);
                                  let
                                  _letpattern11: (evercddl_label, crate::cbordetveraux::cbor_raw)
                                  =
                                      {
                                          let
                                          _il: &[(evercddl_label, crate::cbordetveraux::cbor_raw)]
                                          =
                                              _letpattern10.0;
                                          let
                                          ir: &[(evercddl_label, crate::cbordetveraux::cbor_raw)]
                                          =
                                              _letpattern10.1;
                                          let
                                          i·: &[(evercddl_label, crate::cbordetveraux::cbor_raw)]
                                          =
                                              ir;
                                          (&mut pc)[0] = i·;
                                          res0
                                      };
                                  let ck: evercddl_label = _letpattern11.0;
                                  let cv: crate::cbordetveraux::cbor_raw = _letpattern11.1;
                                  let size0: usize = (&psize)[0];
                                  let _letpattern2: (&mut [u8], &mut [u8]) =
                                      out.split_at_mut(size0);
                                  let _outl1: &[u8] = _letpattern2.0;
                                  let out1: &mut [u8] = _letpattern2.1;
                                  let sz1: usize = serialize_label(ck, out1);
                                  if sz1 == 0usize
                                  { (&mut pres)[0] = false }
                                  else
                                  {
                                      let _letpattern3: (&mut [u8], &mut [u8]) =
                                          out1.split_at_mut(sz1);
                                      let outl2: &[u8] = _letpattern3.0;
                                      let out2: &mut [u8] = _letpattern3.1;
                                      let sz2: usize = serialize_values(cv, out2);
                                      if sz2 == 0usize
                                      { (&mut pres)[0] = false }
                                      else
                                      {
                                          let
                                          _letpattern4:
                                          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                          =
                                              crate::cbordetver::cbor_det_parse(outl2);
                                          match _letpattern4
                                          {
                                              crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                              { v: oo1 }
                                              =>
                                                {
                                                    let
                                                    _letpattern5:
                                                    (crate::cbordetveraux::cbor_raw, &[u8])
                                                    =
                                                        oo1;
                                                    let o1: crate::cbordetveraux::cbor_raw =
                                                        _letpattern5.0;
                                                    let _orem1: &[u8] = _letpattern5.1;
                                                    let
                                                    _letpattern6:
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                                    =
                                                        crate::cbordetver::cbor_det_parse(out2);
                                                    match _letpattern6
                                                    {
                                                        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                        { v: oo2 }
                                                        =>
                                                          {
                                                              let
                                                              _letpattern7:
                                                              (crate::cbordetveraux::cbor_raw,
                                                              &[u8])
                                                              =
                                                                  oo2;
                                                              let
                                                              o2: crate::cbordetveraux::cbor_raw
                                                              =
                                                                  _letpattern7.0;
                                                              let _orem2: &[u8] = _letpattern7.1;
                                                              let
                                                              o:
                                                              crate::cbordetveraux::cbor_map_entry
                                                              =
                                                                  crate::cbordetver::cbor_det_mk_map_entry(
                                                                      o1,
                                                                      o2
                                                                  );
                                                              let is_except: bool =
                                                                  aux_env29_map_constraint_1(o);
                                                              if is_except
                                                              { (&mut pres)[0] = false }
                                                              else
                                                              {
                                                                  let size1: usize =
                                                                      size0.wrapping_add(sz1);
                                                                  let size2: usize =
                                                                      size1.wrapping_add(sz2);
                                                                  let
                                                                  _letpattern8:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size2);
                                                                  let
                                                                  _letpattern80:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      {
                                                                          let s1: &mut [u8] =
                                                                              _letpattern8.0;
                                                                          let s2: &mut [u8] =
                                                                              _letpattern8.1;
                                                                          (s1,s2)
                                                                      };
                                                                  let outl: &mut [u8] =
                                                                      _letpattern80.0;
                                                                  let _outr: &[u8] =
                                                                      _letpattern80.1;
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
                                                          },
                                                        _ => panic!("Incomplete pattern matching")
                                                    }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          }
                                      }
                                  }
                              };
                              let res0: bool = (&pres)[0];
                              let ite: bool =
                                  if res0
                                  {
                                      let c3: &[(evercddl_label, crate::cbordetveraux::cbor_raw)] =
                                          (&pc)[0];
                                      let em: bool = c3.len() == 0usize;
                                      ! em
                                  }
                                  else
                                  { false };
                              cond = ite
                          };
                          (&pres)[0]
                      },
                    either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values::Inr
                    { v: c21 }
                    =>
                      {
                          let
                          mut
                          pc:
                          [map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values;
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
                                  map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
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
                                              crate::cbordetver::cbor_det_map_iterator_is_empty(j);
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
                                              (c3.cddl_map_iterator_impl_validate_ex)(elt);
                                          if ! test_ex
                                          {
                                              let elt_value: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(elt);
                                              let test_value: bool =
                                                  (c3.cddl_map_iterator_impl_validate2)(elt_value);
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
                                  map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
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
                                  let test_key: bool = (i.cddl_map_iterator_impl_validate1)(hd_key);
                                  let mut cond0: bool =
                                      if ! test_key
                                      { true }
                                      else
                                      {
                                          let hd_value: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_value(hd);
                                          let test_value: bool =
                                              (i.cddl_map_iterator_impl_validate2)(hd_value);
                                          if ! test_value
                                          { true }
                                          else
                                          { (i.cddl_map_iterator_impl_validate_ex)(hd) }
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
                                              let hd_value: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(hd2);
                                              let test_value: bool =
                                                  (i.cddl_map_iterator_impl_validate2)(hd_value);
                                              if ! test_value
                                              { true }
                                              else
                                              { (i.cddl_map_iterator_impl_validate_ex)(hd2) }
                                          };
                                      cond0 = ite
                                  };
                                  let hd1: crate::cbordetveraux::cbor_map_entry = (&phd)[0];
                                  let hd_key0: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_key(hd1);
                                  let hd_key_res: evercddl_label =
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
                                  map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
                                  =
                                      map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
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
                                  _letpattern10: (evercddl_label, crate::cbordetveraux::cbor_raw)
                                  =
                                      (hd_key_res,hd_value_res);
                                  let ck: evercddl_label = _letpattern10.0;
                                  let cv: crate::cbordetveraux::cbor_raw = _letpattern10.1;
                                  let size0: usize = (&psize)[0];
                                  let _letpattern2: (&mut [u8], &mut [u8]) =
                                      out.split_at_mut(size0);
                                  let _outl1: &[u8] = _letpattern2.0;
                                  let out1: &mut [u8] = _letpattern2.1;
                                  let sz1: usize = serialize_label(ck, out1);
                                  if sz1 == 0usize
                                  { (&mut pres)[0] = false }
                                  else
                                  {
                                      let _letpattern3: (&mut [u8], &mut [u8]) =
                                          out1.split_at_mut(sz1);
                                      let outl2: &[u8] = _letpattern3.0;
                                      let out2: &mut [u8] = _letpattern3.1;
                                      let sz2: usize = serialize_values(cv, out2);
                                      if sz2 == 0usize
                                      { (&mut pres)[0] = false }
                                      else
                                      {
                                          let
                                          _letpattern4:
                                          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                          =
                                              crate::cbordetver::cbor_det_parse(outl2);
                                          match _letpattern4
                                          {
                                              crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                              { v: oo1 }
                                              =>
                                                {
                                                    let
                                                    _letpattern5:
                                                    (crate::cbordetveraux::cbor_raw, &[u8])
                                                    =
                                                        oo1;
                                                    let o1: crate::cbordetveraux::cbor_raw =
                                                        _letpattern5.0;
                                                    let _orem1: &[u8] = _letpattern5.1;
                                                    let
                                                    _letpattern6:
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                                    =
                                                        crate::cbordetver::cbor_det_parse(out2);
                                                    match _letpattern6
                                                    {
                                                        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                        { v: oo2 }
                                                        =>
                                                          {
                                                              let
                                                              _letpattern7:
                                                              (crate::cbordetveraux::cbor_raw,
                                                              &[u8])
                                                              =
                                                                  oo2;
                                                              let
                                                              o2: crate::cbordetveraux::cbor_raw
                                                              =
                                                                  _letpattern7.0;
                                                              let _orem2: &[u8] = _letpattern7.1;
                                                              let
                                                              o:
                                                              crate::cbordetveraux::cbor_map_entry
                                                              =
                                                                  crate::cbordetver::cbor_det_mk_map_entry(
                                                                      o1,
                                                                      o2
                                                                  );
                                                              let is_except: bool =
                                                                  aux_env29_map_constraint_1(o);
                                                              if is_except
                                                              { (&mut pres)[0] = false }
                                                              else
                                                              {
                                                                  let size1: usize =
                                                                      size0.wrapping_add(sz1);
                                                                  let size2: usize =
                                                                      size1.wrapping_add(sz2);
                                                                  let
                                                                  _letpattern8:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size2);
                                                                  let
                                                                  _letpattern80:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      {
                                                                          let s1: &mut [u8] =
                                                                              _letpattern8.0;
                                                                          let s2: &mut [u8] =
                                                                              _letpattern8.1;
                                                                          (s1,s2)
                                                                      };
                                                                  let outl: &mut [u8] =
                                                                      _letpattern80.0;
                                                                  let _outr: &[u8] =
                                                                      _letpattern80.1;
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
                                                          },
                                                        _ => panic!("Incomplete pattern matching")
                                                    }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          }
                                      }
                                  }
                              };
                              let res0: bool = (&pres)[0];
                              let ite: bool =
                                  if res0
                                  {
                                      let
                                      c3:
                                      map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
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
                                              crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
                                          let elt_key: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(elt);
                                          let test_key: bool =
                                              (c3.cddl_map_iterator_impl_validate1)(elt_key);
                                          if ! ! test_key
                                          {
                                              let test_ex: bool =
                                                  (c3.cddl_map_iterator_impl_validate_ex)(elt);
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
                                          cond0 = ite
                                      };
                                      let em: bool = (&pres1)[0];
                                      ! em
                                  }
                                  else
                                  { false };
                              cond = ite
                          };
                          (&pres)[0]
                      },
                    _ => panic!("Incomplete pattern matching")
                }
            }
            else
            { false }
        };
    if res
    {
        let size: usize = (&psize)[0];
        let count: u64 = (&pcount)[0];
        crate::cbordetver::cbor_det_serialize_map(count, out, size)
    }
    else
    { 0usize }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_COSE_Key_OKP···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_COSE_Key_OKP <'a>, &'a [u8]) }
}

pub fn validate_and_parse_COSE_Key_OKP <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_COSE_Key_OKP···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_COSE_Key_OKP···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_COSE_Key_OKP = parse_COSE_Key_OKP(rl);
                  option__·COSE_Format_evercddl_COSE_Key_OKP···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_COSE_Key_OKP···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn is_empty_iterate_map_evercddl_label_and_evercddl_values(
    i:
    map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
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
            let test_ex: bool = (i.cddl_map_iterator_impl_validate_ex)(elt);
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

pub fn next_iterate_map_evercddl_label_and_evercddl_values <'a>(
    pi:
    &'a mut
    [map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
    <'a>]
) ->
    (evercddl_label <'a>, crate::cbordetveraux::cbor_raw <'a>)
{
    let
    i:
    map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
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
            let hd_value: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_map_entry_value(hd);
            let test_value: bool = (i.cddl_map_iterator_impl_validate2)(hd_value);
            if ! test_value { true } else { (i.cddl_map_iterator_impl_validate_ex)(hd) }
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
                let hd_value: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_map_entry_value(hd2);
                let test_value: bool = (i.cddl_map_iterator_impl_validate2)(hd_value);
                if ! test_value { true } else { (i.cddl_map_iterator_impl_validate_ex)(hd2) }
            };
        cond = ite
    };
    let hd1: crate::cbordetveraux::cbor_map_entry = (&phd)[0];
    let hd_key0: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(hd1);
    let hd_key_res: evercddl_label = (i.cddl_map_iterator_impl_parse1)(hd_key0);
    let hd_value: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_map_entry_value(hd1);
    let hd_value_res: crate::cbordetveraux::cbor_raw = (i.cddl_map_iterator_impl_parse2)(hd_value);
    let j: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry = (&pj)[0];
    let
    i·:
    map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
    =
        map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
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

pub fn validate_COSE_Key(c: crate::cbordetveraux::cbor_raw) -> bool
{ validate_COSE_Key_OKP(c) }

pub type evercddl_COSE_Key <'a> = evercddl_COSE_Key_OKP <'a>;

pub fn uu___is_Mkevercddl_COSE_Key0(projectee: evercddl_COSE_Key_OKP) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_COSE_Key_OKP>(projectee);
    true
}

fn evercddl_COSE_Key_right <'a>(x1: evercddl_COSE_Key_OKP <'a>) -> evercddl_COSE_Key_OKP <'a>
{ x1 }

fn evercddl_COSE_Key_left <'a>(x3: evercddl_COSE_Key_OKP <'a>) -> evercddl_COSE_Key_OKP <'a>
{ x3 }

/**
Parser for evercddl_COSE_Key
*/
pub fn
parse_COSE_Key
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_COSE_Key_OKP
    <'a>
{
    let res1: evercddl_COSE_Key_OKP = parse_COSE_Key_OKP(c);
    evercddl_COSE_Key_right(res1)
}

/**
Serializer for evercddl_COSE_Key
*/
pub fn
serialize_COSE_Key(c: evercddl_COSE_Key_OKP, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_COSE_Key_OKP = evercddl_COSE_Key_left(c);
    serialize_COSE_Key_OKP(c·, out)
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_COSE_Key···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_COSE_Key_OKP <'a>, &'a [u8]) }
}

pub fn validate_and_parse_COSE_Key <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_COSE_Key···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_COSE_Key···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_COSE_Key_OKP = parse_COSE_Key(rl);
                  option__·COSE_Format_evercddl_COSE_Key···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_COSE_Key···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn aux_env32_validate_1(
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
        validate_label(c)
    }
}

pub type aux_env32_type_1 <'a> = evercddl_label <'a>;

pub fn uu___is_Mkaux_env32_type_10(projectee: evercddl_label) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_label>(projectee);
    true
}

fn aux_env32_type_1_right <'a>(x1: evercddl_label <'a>) -> evercddl_label <'a> { x1 }

fn aux_env32_type_1_left <'a>(x3: evercddl_label <'a>) -> evercddl_label <'a> { x3 }

/**
Parser for aux_env32_type_1
*/
pub fn
aux_env32_parse_1
<'a>(c: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>) ->
    evercddl_label
    <'a>
{
    let mut pc: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c; 1usize];
    let x: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
    let res1: evercddl_label = parse_label(x);
    aux_env32_type_1_right(res1)
}

/**
Serializer for aux_env32_type_1
*/
pub fn
aux_env32_serialize_1(
    c: evercddl_label,
    out: &mut [u8],
    out_count: &mut [u64],
    out_size: &mut [usize]
) ->
    bool
{
    let c·: evercddl_label = aux_env32_type_1_left(c);
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

pub fn aux_env32_map_constraint_2(x: crate::cbordetveraux::cbor_map_entry) -> bool
{
    let k: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
    let mt: u8 = crate::cbordetver::cbor_det_major_type(k);
    let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;
    let testk: bool =
        if is_uint
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(k);
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
    let test: bool =
        if testk
        {
            let v1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_value(x);
            let test: bool = validate_int(v1);
            if test { true } else { validate_tstr(v1) }
        }
        else
        { false };
    let test0: bool =
        if test
        { true }
        else
        {
            let k0: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
            let mt0: u8 = crate::cbordetver::cbor_det_major_type(k0);
            let is_uint0: bool = mt0 == crate::cbordetveraux::cbor_major_type_uint64;
            let testk0: bool =
                if is_uint0
                {
                    let v1: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(k0);
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
                { false };
            if testk0
            {
                let v1: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_map_entry_value(x);
                let ty: u8 = crate::cbordetver::cbor_det_major_type(v1);
                if ty == crate::cbordetveraux::cbor_major_type_array
                {
                    let v2: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(v1);
                    let _letpattern: crate::cbordetver::cbor_det_view = v2;
                    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                        match _letpattern
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
                        (&pi)[0];
                    let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
                    let test1: bool =
                        if is_done
                        { false }
                        else
                        {
                            let c: crate::cbordetveraux::cbor_raw =
                                crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                            validate_label(c)
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
                                    crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
                                let cont: bool =
                                    if is_done0
                                    { false }
                                    else
                                    {
                                        let c: crate::cbordetveraux::cbor_raw =
                                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                        validate_label(c)
                                    };
                                if ! cont
                                {
                                    (&mut pi)[0] = i10;
                                    (&mut pcont)[0] = false
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
                            (&pi)[0];
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
    let test1: bool =
        if test0
        { true }
        else
        {
            let k0: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
            let mt0: u8 = crate::cbordetver::cbor_det_major_type(k0);
            let is_uint0: bool = mt0 == crate::cbordetveraux::cbor_major_type_uint64;
            let testk0: bool =
                if is_uint0
                {
                    let v1: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(k0);
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
                { false };
            if testk0
            {
                let v1: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_map_entry_value(x);
                let test1: bool = validate_tstr(v1);
                if test1 { true } else { validate_int(v1) }
            }
            else
            { false }
        };
    let test2: bool =
        if test1
        { true }
        else
        {
            let k0: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
            let mt0: u8 = crate::cbordetver::cbor_det_major_type(k0);
            let is_uint0: bool = mt0 == crate::cbordetveraux::cbor_major_type_uint64;
            let testk0: bool =
                if is_uint0
                {
                    let v1: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(k0);
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
                { false };
            if testk0
            {
                let v1: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_map_entry_value(x);
                validate_bstr(v1)
            }
            else
            { false }
        };
    let test3: bool =
        if test2
        { true }
        else
        {
            let k0: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
            let mt0: u8 = crate::cbordetver::cbor_det_major_type(k0);
            let is_uint0: bool = mt0 == crate::cbordetveraux::cbor_major_type_uint64;
            let testk0: bool =
                if is_uint0
                {
                    let v1: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(k0);
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
                { false };
            if testk0
            {
                let v1: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_map_entry_value(x);
                crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(v1);
                true
            }
            else
            { false }
        };
    if test3
    { true }
    else
    {
        let k0: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_key(x);
        let mt0: u8 = crate::cbordetver::cbor_det_major_type(k0);
        let is_uint0: bool = mt0 == crate::cbordetveraux::cbor_major_type_uint64;
        let testk0: bool =
            if is_uint0
            {
                let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(k0);
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
            { false };
        if testk0
        {
            let v1: crate::cbordetveraux::cbor_raw = crate::cbordetver::cbor_det_map_entry_value(x);
            crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(v1);
            true
        }
        else
        { false }
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
                  crate::cbordetver::cbor_det_map_length(a),
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
                  crate::cbordetver::cbor_det_map_get(m1, c1),
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
                                crate::cbordetver::cbor_det_map_get(m2, c10),
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res11: crate::cbordetveraux::impl_map_group_result =
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
                                                    validate_label(c2)
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
                                                                validate_label(c2)
                                                            };
                                                        if ! cont
                                                        {
                                                            (&mut pi)[0] = i10;
                                                            (&mut pcont)[0] = false
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
                                                    (&pi)[0];
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
                                crate::cbordetver::cbor_det_map_get(m2, c10),
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res110: crate::cbordetveraux::impl_map_group_result =
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
                                    { crate::cbordetveraux::impl_map_group_result::MGFail }
                                },
                              _ => panic!("Incomplete pattern matching")
                          };
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
                                crate::cbordetver::cbor_det_map_get(m2, c10),
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res110: crate::cbordetveraux::impl_map_group_result =
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
                                crate::cbordetver::cbor_det_map_get(m2, c10),
                              _ => panic!("Incomplete pattern matching")
                          };
                      let res110: crate::cbordetveraux::impl_map_group_result =
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
                                              crate::cbordetver::cbor_det_map_get(m3, c11),
                                            _ => panic!("Incomplete pattern matching")
                                        };
                                    let res120: crate::cbordetveraux::impl_map_group_result =
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
                                    match res120
                                    {
                                        crate::cbordetveraux::impl_map_group_result::MGOK =>
                                          crate::cbordetveraux::impl_map_group_result::MGOK,
                                        crate::cbordetveraux::impl_map_group_result::MGFail =>
                                          {
                                              (&mut remaining)[0] = i01;
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
                                let mg1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                                    match _letpattern2
                                    {
                                        crate::cbordetver::cbor_det_view::Map { _0: m2 } =>
                                          crate::cbordetver::cbor_det_map_get(m2, c11),
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                let res120: crate::cbordetveraux::impl_map_group_result =
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
                                let res121: crate::cbordetveraux::impl_map_group_result =
                                    match res120
                                    {
                                        crate::cbordetveraux::impl_map_group_result::MGOK =>
                                          {
                                              let i02: u64 = (&remaining)[0];
                                              let mty2: crate::cbordetver::cbor_det_int_kind =
                                                  crate::cbordetver::cbor_det_int_kind::UInt64;
                                              let c12: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_mk_int64(mty2, 5u64);
                                              let x·2: crate::cbordetver::cbor_det_view =
                                                  crate::cbordetver::cbor_det_destruct(c);
                                              let _letpattern3: crate::cbordetver::cbor_det_view =
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
                                                        crate::cbordetver::cbor_det_map_get(m3, c12),
                                                      _ => panic!("Incomplete pattern matching")
                                                  };
                                              let
                                              res130: crate::cbordetveraux::impl_map_group_result
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
                                              crate::cbordetver::cbor_det_mk_int64(mty2, 6u64);
                                          let x·2: crate::cbordetver::cbor_det_view =
                                              crate::cbordetver::cbor_det_destruct(c);
                                          let _letpattern3: crate::cbordetver::cbor_det_view = x·2;
                                          let
                                          mg2:
                                          crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                          =
                                              match _letpattern3
                                              {
                                                  crate::cbordetver::cbor_det_view::Map
                                                  { _0: m2 }
                                                  => crate::cbordetver::cbor_det_map_get(m2, c12),
                                                  _ => panic!("Incomplete pattern matching")
                                              };
                                          let res130: crate::cbordetveraux::impl_map_group_result =
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
                                          let res131: crate::cbordetveraux::impl_map_group_result =
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
                                          match res131
                                          {
                                              crate::cbordetveraux::impl_map_group_result::MGOK =>
                                                {
                                                    let i020: u64 = (&remaining)[0];
                                                    let mty3: crate::cbordetver::cbor_det_int_kind =
                                                        crate::cbordetver::cbor_det_int_kind::UInt64;
                                                    let c13: crate::cbordetveraux::cbor_raw =
                                                        crate::cbordetver::cbor_det_mk_int64(
                                                            mty3,
                                                            5u64
                                                        );
                                                    let x·3: crate::cbordetver::cbor_det_view =
                                                        crate::cbordetver::cbor_det_destruct(c);
                                                    let
                                                    _letpattern4: crate::cbordetver::cbor_det_view
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
                                                              crate::cbordetver::cbor_det_map_get(
                                                                  m3,
                                                                  c13
                                                              ),
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        };
                                                    let
                                                    res14:
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
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        };
                                                    match res14
                                                    {
                                                        crate::cbordetveraux::impl_map_group_result::MGOK
                                                        =>
                                                          crate::cbordetveraux::impl_map_group_result::MGOK,
                                                        crate::cbordetveraux::impl_map_group_result::MGFail
                                                        =>
                                                          {
                                                              (&mut remaining)[0] = i020;
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
                          let testk: bool = validate_label(k);
                          let test: bool =
                              if testk
                              {
                                  let v11: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_value(chd);
                                  validate_values(v11)
                              }
                              else
                              { false };
                          let test0: bool =
                              if test
                              {
                                  let k0: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_key(chd);
                                  let mt: u8 = crate::cbordetver::cbor_det_major_type(k0);
                                  let is_uint: bool =
                                      mt == crate::cbordetveraux::cbor_major_type_uint64;
                                  let testk0: bool =
                                      if is_uint
                                      {
                                          let v11: crate::cbordetver::cbor_det_view =
                                              crate::cbordetver::cbor_det_destruct(k0);
                                          let _letpattern2: crate::cbordetver::cbor_det_view = v11;
                                          let i: u64 =
                                              match _letpattern2
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
                                      if testk0
                                      {
                                          let v11: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_value(chd);
                                          let test1: bool = validate_int(v11);
                                          if test1 { true } else { validate_tstr(v11) }
                                      }
                                      else
                                      { false };
                                  let test10: bool =
                                      if test1
                                      { true }
                                      else
                                      {
                                          let k1: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(chd);
                                          let mt0: u8 = crate::cbordetver::cbor_det_major_type(k1);
                                          let is_uint0: bool =
                                              mt0 == crate::cbordetveraux::cbor_major_type_uint64;
                                          let testk1: bool =
                                              if is_uint0
                                              {
                                                  let v11: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(k1);
                                                  let
                                                  _letpattern2: crate::cbordetver::cbor_det_view
                                                  =
                                                      v11;
                                                  let i: u64 =
                                                      match _letpattern2
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
                                          if testk1
                                          {
                                              let v11: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(chd);
                                              let ty1: u8 =
                                                  crate::cbordetver::cbor_det_major_type(v11);
                                              if ty1 == crate::cbordetveraux::cbor_major_type_array
                                              {
                                                  let v2: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(v11);
                                                  let
                                                  _letpattern2: crate::cbordetver::cbor_det_view
                                                  =
                                                      v2;
                                                  let
                                                  i:
                                                  crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                                  =
                                                      match _letpattern2
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
                                                      (&pi)[0];
                                                  let is_done: bool =
                                                      crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                          i1
                                                      );
                                                  let test11: bool =
                                                      if is_done
                                                      { false }
                                                      else
                                                      {
                                                          let c10: crate::cbordetveraux::cbor_raw =
                                                              crate::cbordetver::cbor_det_array_iterator_next(
                                                                  &mut pi
                                                              );
                                                          validate_label(c10)
                                                      };
                                                  let b_success: bool =
                                                      if test11
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
                                                                      c10:
                                                                      crate::cbordetveraux::cbor_raw
                                                                      =
                                                                          crate::cbordetver::cbor_det_array_iterator_next(
                                                                              &mut pi
                                                                          );
                                                                      validate_label(c10)
                                                                  };
                                                              if ! cont
                                                              {
                                                                  (&mut pi)[0] = i10;
                                                                  (&mut pcont)[0] = false
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
                                                          (&pi)[0];
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
                                  let test11: bool =
                                      if test10
                                      { true }
                                      else
                                      {
                                          let k1: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(chd);
                                          let mt0: u8 = crate::cbordetver::cbor_det_major_type(k1);
                                          let is_uint0: bool =
                                              mt0 == crate::cbordetveraux::cbor_major_type_uint64;
                                          let testk1: bool =
                                              if is_uint0
                                              {
                                                  let v11: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(k1);
                                                  let
                                                  _letpattern2: crate::cbordetver::cbor_det_view
                                                  =
                                                      v11;
                                                  let i: u64 =
                                                      match _letpattern2
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
                                          if testk1
                                          {
                                              let v11: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(chd);
                                              let test2: bool = validate_tstr(v11);
                                              if test2 { true } else { validate_int(v11) }
                                          }
                                          else
                                          { false }
                                      };
                                  let test12: bool =
                                      if test11
                                      { true }
                                      else
                                      {
                                          let k1: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(chd);
                                          let mt0: u8 = crate::cbordetver::cbor_det_major_type(k1);
                                          let is_uint0: bool =
                                              mt0 == crate::cbordetveraux::cbor_major_type_uint64;
                                          let testk1: bool =
                                              if is_uint0
                                              {
                                                  let v11: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(k1);
                                                  let
                                                  _letpattern2: crate::cbordetver::cbor_det_view
                                                  =
                                                      v11;
                                                  let i: u64 =
                                                      match _letpattern2
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
                                          if testk1
                                          {
                                              let v11: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(chd);
                                              validate_bstr(v11)
                                          }
                                          else
                                          { false }
                                      };
                                  let test13: bool =
                                      if test12
                                      { true }
                                      else
                                      {
                                          let k1: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(chd);
                                          let mt0: u8 = crate::cbordetver::cbor_det_major_type(k1);
                                          let is_uint0: bool =
                                              mt0 == crate::cbordetveraux::cbor_major_type_uint64;
                                          let testk1: bool =
                                              if is_uint0
                                              {
                                                  let v11: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(k1);
                                                  let
                                                  _letpattern2: crate::cbordetver::cbor_det_view
                                                  =
                                                      v11;
                                                  let i: u64 =
                                                      match _letpattern2
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
                                          if testk1
                                          {
                                              let v11: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(chd);
                                              crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(
                                                  v11
                                              );
                                              true
                                          }
                                          else
                                          { false }
                                      };
                                  let test14: bool =
                                      if test13
                                      { true }
                                      else
                                      {
                                          let k1: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(chd);
                                          let mt0: u8 = crate::cbordetver::cbor_det_major_type(k1);
                                          let is_uint0: bool =
                                              mt0 == crate::cbordetveraux::cbor_major_type_uint64;
                                          let testk1: bool =
                                              if is_uint0
                                              {
                                                  let v11: crate::cbordetver::cbor_det_view =
                                                      crate::cbordetver::cbor_det_destruct(k1);
                                                  let
                                                  _letpattern2: crate::cbordetver::cbor_det_view
                                                  =
                                                      v11;
                                                  let i: u64 =
                                                      match _letpattern2
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
                                          if testk1
                                          {
                                              let v11: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(chd);
                                              crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(
                                                  v11
                                              );
                                              true
                                          }
                                          else
                                          { false }
                                      };
                                  ! test14
                              }
                              else
                              { false };
                          let test1: bool = ! test0;
                          if ! test1
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
option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr
<'a>
{
    None,
    Some { v: evercddl_label_ugly <'a> }
}

#[derive(PartialEq, Clone, Copy)]
pub struct
array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env32_type_1
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
either__CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1
<'a>
{
    Inl { v: &'a [evercddl_label <'a>] },
    Inr
    {
        v:
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env32_type_1
        <'a>
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1
<'a>
{
    None,
    Some
    {
        v:
        either__CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1
        <'a>
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum either__COSE_Format_evercddl_tstr_COSE_Format_evercddl_int <'a>
{
    Inl { v: &'a [u8] },
    Inr { v: evercddl_int }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int
<'a>
{
    None,
    Some { v: either__COSE_Format_evercddl_tstr_COSE_Format_evercddl_int <'a> }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__COSE_Format_evercddl_everparsenomatch
{
    None,
    Some { v: evercddl_everparsenomatch }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_·FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·
<'a>
{
    Inl { v: (&'a [u8], option__COSE_Format_evercddl_everparsenomatch) },
    Inr
    {
        v:
        (option__COSE_Format_evercddl_everparsenomatch,
        option__COSE_Format_evercddl_everparsenomatch)
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_FStar_Pervasives_either··COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·
<'a>
{
    Inl { v: (&'a [u8], option__COSE_Format_evercddl_everparsenomatch) },
    Inr
    {
        v:
        either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_·FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·
        <'a>
    }
}

#[derive(PartialEq, Clone, Copy)]
pub struct evercddl_header_map <'a>
{
    pub intkey1:
    option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr <'a>,
    pub intkey2:
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1
    <'a>,
    pub intkey3:
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int <'a>,
    pub intkey4: option__COSE_Format_evercddl_bstr <'a>,
    pub _x0:
    either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_FStar_Pervasives_either··COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·
    <'a>,
    pub _x1:
    either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values
    <'a>
}

pub fn uu___is_Mkevercddl_header_map0(projectee: evercddl_header_map) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_header_map>(projectee);
    true
}

fn evercddl_header_map_right <'a>(
    x6:
    (((((option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr
    <'a>,
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1
    <'a>),
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int
    <'a>),
    option__COSE_Format_evercddl_bstr
    <'a>),
    either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_FStar_Pervasives_either··COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·
    <'a>),
    either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values
    <'a>)
) ->
    evercddl_header_map
    <'a>
{
    match x6
    {
        (((((x7,x8),x9),x10),x11),x12) =>
          evercddl_header_map
          { intkey1: x7, intkey2: x8, intkey3: x9, intkey4: x10, _x0: x11, _x1: x12 }
    }
}

fn evercddl_header_map_left <'a>(x13: evercddl_header_map <'a>) ->
    (((((option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr
    <'a>,
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1
    <'a>),
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int
    <'a>),
    option__COSE_Format_evercddl_bstr
    <'a>),
    either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_FStar_Pervasives_either··COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·
    <'a>),
    either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values
    <'a>)
{
    let x21: option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr =
        x13.intkey1;
    let
    x22:
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1
    =
        x13.intkey2;
    let x23: option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int =
        x13.intkey3;
    let x24: option__COSE_Format_evercddl_bstr = x13.intkey4;
    let
    x25:
    either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_FStar_Pervasives_either··COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·
    =
        x13._x0;
    let
    x26:
    either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values
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
    evercddl_header_map
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
              crate::cbordetver::cbor_det_map_get(m3, c1),
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
    let w1: option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr =
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
                      crate::cbordetver::cbor_det_map_get(m3, c10),
                    _ => panic!("Incomplete pattern matching")
                };
            let _letpattern1: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow;
            let w1: evercddl_label_ugly =
                match _letpattern1
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      {
                          let test: bool = validate_int(w);
                          if test
                          {
                              let res: evercddl_int = parse_int(w);
                              evercddl_label_ugly::Inl { v: res }
                          }
                          else
                          {
                              let res: &[u8] = parse_tstr(w);
                              evercddl_label_ugly::Inr { v: res }
                          }
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr::Some
            { v: w1 }
        }
        else
        {
            option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr::None
        };
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
              crate::cbordetver::cbor_det_map_get(m3, c10),
            _ => panic!("Incomplete pattern matching")
        };
    let test10: crate::cbordetveraux::impl_map_group_result =
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
                                  validate_label(c2)
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
                                              validate_label(c2)
                                          };
                                      if ! cont
                                      {
                                          (&mut pi)[0] = i10;
                                          (&mut pcont)[0] = false
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
                                  (&pi)[0];
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
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1
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
                      crate::cbordetver::cbor_det_map_get(m3, c11),
                    _ => panic!("Incomplete pattern matching")
                };
            let _letpattern2: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow;
            let
            w11:
            either__CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1
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
                                    crate::cbordetver::cbor_det_array_iterator_start(a),
                                  _ => panic!("Incomplete pattern matching")
                              };
                          let
                          i:
                          array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env32_type_1
                          =
                              array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env32_type_1
                              {
                                  cddl_array_iterator_contents: ar,
                                  cddl_array_iterator_impl_validate: aux_env32_validate_1,
                                  cddl_array_iterator_impl_parse: aux_env32_parse_1
                              };
                          either__CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1::Inr
                          { v: i }
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1::Some
            { v: w11 }
        }
        else
        {
            option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1::None
        };
    let
    w10:
    (option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr,
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1)
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
              crate::cbordetver::cbor_det_map_get(m3, c11),
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
    let w20: option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int =
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
                      crate::cbordetver::cbor_det_map_get(m3, c12),
                    _ => panic!("Incomplete pattern matching")
                };
            let _letpattern3: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow;
            let w11: either__COSE_Format_evercddl_tstr_COSE_Format_evercddl_int =
                match _letpattern3
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      {
                          let test: bool = validate_tstr(w);
                          if test
                          {
                              let res: &[u8] = parse_tstr(w);
                              either__COSE_Format_evercddl_tstr_COSE_Format_evercddl_int::Inl
                              { v: res }
                          }
                          else
                          {
                              let res: evercddl_int = parse_int(w);
                              either__COSE_Format_evercddl_tstr_COSE_Format_evercddl_int::Inr
                              { v: res }
                          }
                      },
                    _ => panic!("Incomplete pattern matching")
                };
            option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int::Some
            { v: w11 }
        }
        else
        {
            option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int::None
        };
    let
    w11:
    ((option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr,
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1),
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int)
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
              crate::cbordetver::cbor_det_map_get(m3, c12),
            _ => panic!("Incomplete pattern matching")
        };
    let test12: crate::cbordetveraux::impl_map_group_result =
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
                  { crate::cbordetveraux::impl_map_group_result::MGFail }
              },
            _ => panic!("Incomplete pattern matching")
        };
    let w21: option__COSE_Format_evercddl_bstr =
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
                      crate::cbordetver::cbor_det_map_get(m3, c13),
                    _ => panic!("Incomplete pattern matching")
                };
            let _letpattern4: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow;
            let w110: &[u8] =
                match _letpattern4
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      parse_bstr(w),
                    _ => panic!("Incomplete pattern matching")
                };
            option__COSE_Format_evercddl_bstr::Some { v: w110 }
        }
        else
        { option__COSE_Format_evercddl_bstr::None };
    let
    w12:
    (((option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr,
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1),
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int),
    option__COSE_Format_evercddl_bstr)
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
              crate::cbordetver::cbor_det_map_get(m3, c13),
            _ => panic!("Incomplete pattern matching")
        };
    let res1: crate::cbordetveraux::impl_map_group_result =
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
    let test13: crate::cbordetveraux::impl_map_group_result =
        match res1
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
                            crate::cbordetver::cbor_det_map_get(m4, c14),
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
                  match res11
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
                  }
              },
            crate::cbordetveraux::impl_map_group_result::MGFail =>
              crate::cbordetveraux::impl_map_group_result::MGFail,
            crate::cbordetveraux::impl_map_group_result::MGCutFail =>
              crate::cbordetveraux::impl_map_group_result::MGCutFail,
            _ => panic!("Precondition of the function most likely violated")
        };
    let
    w22:
    either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_FStar_Pervasives_either··COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·
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
                      crate::cbordetver::cbor_det_map_get(m3, c14),
                    _ => panic!("Incomplete pattern matching")
                };
            let _letpattern5: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow;
            let w110: &[u8] =
                match _letpattern5
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: w } =>
                      parse_bstr(w),
                    _ => panic!("Incomplete pattern matching")
                };
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
                      crate::cbordetver::cbor_det_map_get(m3, c15),
                    _ => panic!("Incomplete pattern matching")
                };
            let test110: crate::cbordetveraux::impl_map_group_result =
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
            let w22: option__COSE_Format_evercddl_everparsenomatch =
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
                              crate::cbordetver::cbor_det_map_get(m3, c16),
                            _ => panic!("Incomplete pattern matching")
                        };
                    let _letpattern8: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow0;
                    let w120: evercddl_everparsenomatch =
                        match _letpattern8
                        {
                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                            { v: w }
                            => parse_everparsenomatch(w),
                            _ => panic!("Incomplete pattern matching")
                        };
                    option__COSE_Format_evercddl_everparsenomatch::Some { v: w120 }
                }
                else
                { option__COSE_Format_evercddl_everparsenomatch::None };
            let w111: (&[u8], option__COSE_Format_evercddl_everparsenomatch) = (w110,w22);
            either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_FStar_Pervasives_either··COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·::Inl
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
                      crate::cbordetver::cbor_det_map_get(m3, c14),
                    _ => panic!("Incomplete pattern matching")
                };
            let res10: crate::cbordetveraux::impl_map_group_result =
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
            let test110: crate::cbordetveraux::impl_map_group_result =
                match res10
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
                                    crate::cbordetver::cbor_det_map_get(m4, c15),
                                  _ => panic!("Incomplete pattern matching")
                              };
                          let res11: crate::cbordetveraux::impl_map_group_result =
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
                          match res11
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
                          }
                      },
                    crate::cbordetveraux::impl_map_group_result::MGFail =>
                      crate::cbordetveraux::impl_map_group_result::MGFail,
                    crate::cbordetveraux::impl_map_group_result::MGCutFail =>
                      crate::cbordetveraux::impl_map_group_result::MGCutFail,
                    _ => panic!("Precondition of the function most likely violated")
                };
            let
            w22:
            either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_·FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·
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
                              crate::cbordetver::cbor_det_map_get(m3, c15),
                            _ => panic!("Incomplete pattern matching")
                        };
                    let _letpattern6: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = ow;
                    let w110: &[u8] =
                        match _letpattern6
                        {
                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                            { v: w }
                            => parse_bstr(w),
                            _ => panic!("Incomplete pattern matching")
                        };
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
                              crate::cbordetver::cbor_det_map_get(m3, c16),
                            _ => panic!("Incomplete pattern matching")
                        };
                    let test120: crate::cbordetveraux::impl_map_group_result =
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
                    let w22: option__COSE_Format_evercddl_everparsenomatch =
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
                                      crate::cbordetver::cbor_det_map_get(m3, c17),
                                    _ => panic!("Incomplete pattern matching")
                                };
                            let
                            _letpattern9: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                            =
                                ow0;
                            let w120: evercddl_everparsenomatch =
                                match _letpattern9
                                {
                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                    { v: w }
                                    => parse_everparsenomatch(w),
                                    _ => panic!("Incomplete pattern matching")
                                };
                            option__COSE_Format_evercddl_everparsenomatch::Some { v: w120 }
                        }
                        else
                        { option__COSE_Format_evercddl_everparsenomatch::None };
                    let w111: (&[u8], option__COSE_Format_evercddl_everparsenomatch) = (w110,w22);
                    either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_·FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·::Inl
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
                              crate::cbordetver::cbor_det_map_get(m3, c15),
                            _ => panic!("Incomplete pattern matching")
                        };
                    let test120: crate::cbordetveraux::impl_map_group_result =
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
                    let w110: option__COSE_Format_evercddl_everparsenomatch =
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
                                      crate::cbordetver::cbor_det_map_get(m3, c16),
                                    _ => panic!("Incomplete pattern matching")
                                };
                            let
                            _letpattern7: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                            =
                                ow;
                            let w110: evercddl_everparsenomatch =
                                match _letpattern7
                                {
                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                    { v: w }
                                    => parse_everparsenomatch(w),
                                    _ => panic!("Incomplete pattern matching")
                                };
                            option__COSE_Format_evercddl_everparsenomatch::Some { v: w110 }
                        }
                        else
                        { option__COSE_Format_evercddl_everparsenomatch::None };
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
                              crate::cbordetver::cbor_det_map_get(m3, c16),
                            _ => panic!("Incomplete pattern matching")
                        };
                    let test121: crate::cbordetveraux::impl_map_group_result =
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
                    let w22: option__COSE_Format_evercddl_everparsenomatch =
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
                                      crate::cbordetver::cbor_det_map_get(m3, c17),
                                    _ => panic!("Incomplete pattern matching")
                                };
                            let
                            _letpattern8: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                            =
                                ow;
                            let w120: evercddl_everparsenomatch =
                                match _letpattern8
                                {
                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                    { v: w }
                                    => parse_everparsenomatch(w),
                                    _ => panic!("Incomplete pattern matching")
                                };
                            option__COSE_Format_evercddl_everparsenomatch::Some { v: w120 }
                        }
                        else
                        { option__COSE_Format_evercddl_everparsenomatch::None };
                    let
                    w23:
                    (option__COSE_Format_evercddl_everparsenomatch,
                    option__COSE_Format_evercddl_everparsenomatch)
                    =
                        (w110,w22);
                    either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_·FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·::Inr
                    { v: w23 }
                };
            either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_FStar_Pervasives_either··COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·::Inr
            { v: w22 }
        };
    let
    w13:
    ((((option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr,
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1),
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int),
    option__COSE_Format_evercddl_bstr),
    either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_FStar_Pervasives_either··COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·)
    =
        (w12,w22);
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern4: crate::cbordetver::cbor_det_view = v1;
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
        match _letpattern4
        {
            crate::cbordetver::cbor_det_view::Map { _0: a } =>
              crate::cbordetver::cbor_det_map_iterator_start(a),
            _ => panic!("Incomplete pattern matching")
        };
    let
    rres:
    map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
    =
        map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
        {
            cddl_map_iterator_contents: i,
            cddl_map_iterator_impl_validate1: validate_label,
            cddl_map_iterator_impl_parse1: parse_label,
            cddl_map_iterator_impl_validate_ex: aux_env32_map_constraint_2,
            cddl_map_iterator_impl_validate2: validate_values,
            cddl_map_iterator_impl_parse2: parse_values
        };
    let
    w23:
    either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values
    =
        either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values::Inr
        { v: rres };
    let
    res10:
    (((((option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr,
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1),
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int),
    option__COSE_Format_evercddl_bstr),
    either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_FStar_Pervasives_either··COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·),
    either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values)
    =
        (w13,w23);
    evercddl_header_map_right(res10)
}

/**
Serializer for evercddl_header_map
*/
pub fn
serialize_header_map(c: evercddl_header_map, out: &mut [u8]) ->
    usize
{
    let
    c·:
    (((((option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr,
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1),
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int),
    option__COSE_Format_evercddl_bstr),
    either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_FStar_Pervasives_either··COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·),
    either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values)
    =
        evercddl_header_map_left(c);
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let
    _letpattern:
    (((((option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr,
    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1),
    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int),
    option__COSE_Format_evercddl_bstr),
    either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_FStar_Pervasives_either··COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·),
    either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values)
    =
        c·;
    let res: bool =
        {
            let
            c1:
            ((((option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr,
            option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1),
            option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int),
            option__COSE_Format_evercddl_bstr),
            either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_FStar_Pervasives_either··COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·)
            =
                _letpattern.0;
            let
            c2:
            either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values
            =
                _letpattern.1;
            let
            _letpattern1:
            ((((option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr,
            option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1),
            option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int),
            option__COSE_Format_evercddl_bstr),
            either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_FStar_Pervasives_either··COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·)
            =
                c1;
            let res1: bool =
                {
                    let
                    c11:
                    (((option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr,
                    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1),
                    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int),
                    option__COSE_Format_evercddl_bstr)
                    =
                        _letpattern1.0;
                    let
                    c21:
                    either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_FStar_Pervasives_either··COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·
                    =
                        _letpattern1.1;
                    let
                    _letpattern2:
                    (((option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr,
                    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1),
                    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int),
                    option__COSE_Format_evercddl_bstr)
                    =
                        c11;
                    let res1: bool =
                        {
                            let
                            c12:
                            ((option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr,
                            option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1),
                            option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int)
                            =
                                _letpattern2.0;
                            let c22: option__COSE_Format_evercddl_bstr = _letpattern2.1;
                            let
                            _letpattern3:
                            ((option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr,
                            option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1),
                            option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int)
                            =
                                c12;
                            let res1: bool =
                                {
                                    let
                                    c13:
                                    (option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr,
                                    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1)
                                    =
                                        _letpattern3.0;
                                    let
                                    c23:
                                    option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int
                                    =
                                        _letpattern3.1;
                                    let
                                    _letpattern4:
                                    (option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr,
                                    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1)
                                    =
                                        c13;
                                    let res1: bool =
                                        {
                                            let
                                            c14:
                                            option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr
                                            =
                                                _letpattern4.0;
                                            let
                                            c24:
                                            option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1
                                            =
                                                _letpattern4.1;
                                            let res1: bool =
                                                match c14
                                                {
                                                    option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr::Some
                                                    { v: c15 }
                                                    =>
                                                      {
                                                          let count: u64 = (&pcount)[0];
                                                          if count < 18446744073709551615u64
                                                          {
                                                              let size0: usize = (&psize)[0];
                                                              let
                                                              _letpattern5: (&mut [u8], &mut [u8])
                                                              =
                                                                  out.split_at_mut(size0);
                                                              let _out0: &[u8] = _letpattern5.0;
                                                              let out1: &mut [u8] = _letpattern5.1;
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
                                                                          evercddl_label_ugly::Inl
                                                                          { v: c16 }
                                                                          =>
                                                                            serialize_int(c16, out2),
                                                                          evercddl_label_ugly::Inr
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
                                                                      _letpattern7:
                                                                      (&mut [u8], &mut [u8])
                                                                      =
                                                                          out.split_at_mut(size2);
                                                                      let out012: &mut [u8] =
                                                                          _letpattern7.0;
                                                                      let res0: bool =
                                                                          crate::cbordetver::cbor_det_serialize_map_insert(
                                                                              out012,
                                                                              size0,
                                                                              size1
                                                                          );
                                                                      if res0
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
                                                          { false }
                                                      },
                                                    option__FStar_Pervasives_either·COSE_Format_evercddl_int·COSE_Format_evercddl_tstr::None
                                                    => true,
                                                    _ => panic!("Incomplete pattern matching")
                                                };
                                            if res1
                                            {
                                                match c24
                                                {
                                                    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1::Some
                                                    { v: c15 }
                                                    =>
                                                      {
                                                          let count: u64 = (&pcount)[0];
                                                          if count < 18446744073709551615u64
                                                          {
                                                              let size0: usize = (&psize)[0];
                                                              let
                                                              _letpattern5: (&mut [u8], &mut [u8])
                                                              =
                                                                  out.split_at_mut(size0);
                                                              let _out0: &[u8] = _letpattern5.0;
                                                              let out1: &mut [u8] = _letpattern5.1;
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
                                                                  _letpattern6:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size1);
                                                                  let _out01: &[u8] =
                                                                      _letpattern6.0;
                                                                  let out2: &mut [u8] =
                                                                      _letpattern6.1;
                                                                  let mut pcount1: [u64; 1] =
                                                                      [0u64; 1usize];
                                                                  let mut psize1: [usize; 1] =
                                                                      [0usize; 1usize];
                                                                  let res0: bool =
                                                                      match c15
                                                                      {
                                                                          either__CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1::Inl
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
                                                                                let res0: bool =
                                                                                    (&pres)[0];
                                                                                let mut cond: bool =
                                                                                    if res0
                                                                                    {
                                                                                        let
                                                                                        i: usize
                                                                                        =
                                                                                            (&pi)[0];
                                                                                        i < slen
                                                                                    }
                                                                                    else
                                                                                    { false };
                                                                                while
                                                                                cond
                                                                                {
                                                                                    let i: usize =
                                                                                        (&pi)[0];
                                                                                    let
                                                                                    x:
                                                                                    evercddl_label
                                                                                    =
                                                                                        c16[i];
                                                                                    let res2: bool =
                                                                                        aux_env32_serialize_1(
                                                                                            x,
                                                                                            out2,
                                                                                            &mut
                                                                                            pcount1,
                                                                                            &mut
                                                                                            psize1
                                                                                        );
                                                                                    if res2
                                                                                    {
                                                                                        let
                                                                                        i·: usize
                                                                                        =
                                                                                            i.wrapping_add(
                                                                                                1usize
                                                                                            );
                                                                                        (&mut pi)[0] =
                                                                                            i·
                                                                                    }
                                                                                    else
                                                                                    {
                                                                                        (&mut pres)[0] =
                                                                                            false
                                                                                    };
                                                                                    let res3: bool =
                                                                                        (&pres)[0];
                                                                                    let ite: bool =
                                                                                        if res3
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
                                                                                        { false };
                                                                                    cond = ite
                                                                                };
                                                                                (&pres)[0]
                                                                            },
                                                                          either__CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1::Inr
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
                                                                                    [array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env32_type_1;
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
                                                                                    let res0: bool =
                                                                                        (&pres)[0];
                                                                                    let
                                                                                    mut cond: bool
                                                                                    =
                                                                                        if res0
                                                                                        {
                                                                                            let
                                                                                            c30:
                                                                                            array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env32_type_1
                                                                                            =
                                                                                                (&pc)[0];
                                                                                            let
                                                                                            em1:
                                                                                            bool
                                                                                            =
                                                                                                crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                                                                    c30.cddl_array_iterator_contents
                                                                                                );
                                                                                            ! em1
                                                                                        }
                                                                                        else
                                                                                        { false };
                                                                                    while
                                                                                    cond
                                                                                    {
                                                                                        let
                                                                                        i:
                                                                                        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env32_type_1
                                                                                        =
                                                                                            (&pc)[0];
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
                                                                                        _test: bool
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
                                                                                        len1: u64
                                                                                        =
                                                                                            crate::cbordetver::cbor_det_array_iterator_length(
                                                                                                ji
                                                                                            );
                                                                                        let
                                                                                        j:
                                                                                        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env32_type_1
                                                                                        =
                                                                                            array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env32_type_1
                                                                                            {
                                                                                                cddl_array_iterator_contents:
                                                                                                ji,
                                                                                                cddl_array_iterator_impl_validate:
                                                                                                i.cddl_array_iterator_impl_validate,
                                                                                                cddl_array_iterator_impl_parse:
                                                                                                i.cddl_array_iterator_impl_parse
                                                                                            };
                                                                                        (&mut pc)[0] =
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
                                                                                        res2: bool
                                                                                        =
                                                                                            aux_env32_serialize_1(
                                                                                                x,
                                                                                                out2,
                                                                                                &mut
                                                                                                pcount1,
                                                                                                &mut
                                                                                                psize1
                                                                                            );
                                                                                        if ! res2
                                                                                        {
                                                                                            (&mut
                                                                                            pres)[0] =
                                                                                                false
                                                                                        };
                                                                                        let
                                                                                        res3: bool
                                                                                        =
                                                                                            (&pres)[0];
                                                                                        let
                                                                                        ite: bool
                                                                                        =
                                                                                            if res3
                                                                                            {
                                                                                                let
                                                                                                c30:
                                                                                                array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env32_type_1
                                                                                                =
                                                                                                    (&pc)[0];
                                                                                                let
                                                                                                em1:
                                                                                                bool
                                                                                                =
                                                                                                    crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                                                                        c30.cddl_array_iterator_contents
                                                                                                    );
                                                                                                !
                                                                                                em1
                                                                                            }
                                                                                            else
                                                                                            {
                                                                                                false
                                                                                            };
                                                                                        cond = ite
                                                                                    };
                                                                                    (&pres)[0]
                                                                                }
                                                                            },
                                                                          _ =>
                                                                            panic!(
                                                                                "Incomplete pattern matching"
                                                                            )
                                                                      };
                                                                  let res2: usize =
                                                                      if res0
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
                                                                  if res2 > 0usize
                                                                  {
                                                                      let size2: usize =
                                                                          size1.wrapping_add(res2);
                                                                      let
                                                                      _letpattern7:
                                                                      (&mut [u8], &mut [u8])
                                                                      =
                                                                          out.split_at_mut(size2);
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
                                                          { false }
                                                      },
                                                    option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env32_type_1·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env32_type_1::None
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
                                            option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int::Some
                                            { v: c14 }
                                            =>
                                              {
                                                  let count: u64 = (&pcount)[0];
                                                  if count < 18446744073709551615u64
                                                  {
                                                      let size0: usize = (&psize)[0];
                                                      let _letpattern40: (&mut [u8], &mut [u8]) =
                                                          out.split_at_mut(size0);
                                                      let _out0: &[u8] = _letpattern40.0;
                                                      let out1: &mut [u8] = _letpattern40.1;
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
                                                          let _letpattern5: (&mut [u8], &mut [u8]) =
                                                              out.split_at_mut(size1);
                                                          let _out01: &[u8] = _letpattern5.0;
                                                          let out2: &mut [u8] = _letpattern5.1;
                                                          let res2: usize =
                                                              match c14
                                                              {
                                                                  either__COSE_Format_evercddl_tstr_COSE_Format_evercddl_int::Inl
                                                                  { v: c15 }
                                                                  => serialize_tstr(c15, out2),
                                                                  either__COSE_Format_evercddl_tstr_COSE_Format_evercddl_int::Inr
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
                                                              _letpattern6: (&mut [u8], &mut [u8])
                                                              =
                                                                  out.split_at_mut(size2);
                                                              let out012: &mut [u8] =
                                                                  _letpattern6.0;
                                                              let res0: bool =
                                                                  crate::cbordetver::cbor_det_serialize_map_insert(
                                                                      out012,
                                                                      size0,
                                                                      size1
                                                                  );
                                                              if res0
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
                                                  { false }
                                              },
                                            option__FStar_Pervasives_either·COSE_Format_evercddl_tstr·COSE_Format_evercddl_int::None
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
                                    option__COSE_Format_evercddl_bstr::Some { v: c13 } =>
                                      {
                                          let count: u64 = (&pcount)[0];
                                          if count < 18446744073709551615u64
                                          {
                                              let size0: usize = (&psize)[0];
                                              let _letpattern30: (&mut [u8], &mut [u8]) =
                                                  out.split_at_mut(size0);
                                              let _out0: &[u8] = _letpattern30.0;
                                              let out1: &mut [u8] = _letpattern30.1;
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
                                                  let _letpattern4: (&mut [u8], &mut [u8]) =
                                                      out.split_at_mut(size1);
                                                  let _out01: &[u8] = _letpattern4.0;
                                                  let out2: &mut [u8] = _letpattern4.1;
                                                  let res2: usize = serialize_bstr(c13, out2);
                                                  if res2 > 0usize
                                                  {
                                                      let size2: usize = size1.wrapping_add(res2);
                                                      let _letpattern5: (&mut [u8], &mut [u8]) =
                                                          out.split_at_mut(size2);
                                                      let out012: &mut [u8] = _letpattern5.0;
                                                      let res0: bool =
                                                          crate::cbordetver::cbor_det_serialize_map_insert(
                                                              out012,
                                                              size0,
                                                              size1
                                                          );
                                                      if res0
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
                                          { false }
                                      },
                                    option__COSE_Format_evercddl_bstr::None => true,
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
                            either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_FStar_Pervasives_either··COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·::Inl
                            { v: c12 }
                            =>
                              {
                                  let
                                  _letpattern20:
                                  (&[u8], option__COSE_Format_evercddl_everparsenomatch)
                                  =
                                      c12;
                                  let c13: &[u8] = _letpattern20.0;
                                  let c22: option__COSE_Format_evercddl_everparsenomatch =
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
                                              let _letpattern4: (&mut [u8], &mut [u8]) =
                                                  out.split_at_mut(size1);
                                              let _out01: &[u8] = _letpattern4.0;
                                              let out2: &mut [u8] = _letpattern4.1;
                                              let res2: usize = serialize_bstr(c13, out2);
                                              if res2 > 0usize
                                              {
                                                  let size2: usize = size1.wrapping_add(res2);
                                                  let _letpattern5: (&mut [u8], &mut [u8]) =
                                                      out.split_at_mut(size2);
                                                  let out012: &mut [u8] = _letpattern5.0;
                                                  let res0: bool =
                                                      crate::cbordetver::cbor_det_serialize_map_insert(
                                                          out012,
                                                          size0,
                                                          size1
                                                      );
                                                  if res0
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
                                  if res11
                                  {
                                      match c22
                                      {
                                          option__COSE_Format_evercddl_everparsenomatch::Some
                                          { v: c14 }
                                          =>
                                            {
                                                let count0: u64 = (&pcount)[0];
                                                if count0 < 18446744073709551615u64
                                                {
                                                    let size0: usize = (&psize)[0];
                                                    let _letpattern3: (&mut [u8], &mut [u8]) =
                                                        out.split_at_mut(size0);
                                                    let _out0: &[u8] = _letpattern3.0;
                                                    let out1: &mut [u8] = _letpattern3.1;
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
                                                        let _letpattern4: (&[u8], &[u8]) =
                                                            out.split_at(size1);
                                                        let _out01: &[u8] = _letpattern4.0;
                                                        let out2: &[u8] = _letpattern4.1;
                                                        let res2: usize =
                                                            serialize_everparsenomatch(c14, out2);
                                                        if res2 > 0usize
                                                        {
                                                            let size2: usize =
                                                                size1.wrapping_add(res2);
                                                            let
                                                            _letpattern5: (&mut [u8], &mut [u8])
                                                            =
                                                                out.split_at_mut(size2);
                                                            let out012: &mut [u8] = _letpattern5.0;
                                                            let res0: bool =
                                                                crate::cbordetver::cbor_det_serialize_map_insert(
                                                                    out012,
                                                                    size0,
                                                                    size1
                                                                );
                                                            if res0
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
                                                { false }
                                            },
                                          option__COSE_Format_evercddl_everparsenomatch::None =>
                                            true,
                                          _ => panic!("Incomplete pattern matching")
                                      }
                                  }
                                  else
                                  { false }
                              },
                            either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_FStar_Pervasives_either··COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·::Inr
                            { v: c22 }
                            =>
                              match c22
                              {
                                  either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_·FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·::Inl
                                  { v: c12 }
                                  =>
                                    {
                                        let
                                        _letpattern20:
                                        (&[u8], option__COSE_Format_evercddl_everparsenomatch)
                                        =
                                            c12;
                                        let c13: &[u8] = _letpattern20.0;
                                        let c23: option__COSE_Format_evercddl_everparsenomatch =
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
                                                    let _letpattern4: (&mut [u8], &mut [u8]) =
                                                        out.split_at_mut(size1);
                                                    let _out01: &[u8] = _letpattern4.0;
                                                    let out2: &mut [u8] = _letpattern4.1;
                                                    let res2: usize = serialize_bstr(c13, out2);
                                                    if res2 > 0usize
                                                    {
                                                        let size2: usize = size1.wrapping_add(res2);
                                                        let _letpattern5: (&mut [u8], &mut [u8]) =
                                                            out.split_at_mut(size2);
                                                        let out012: &mut [u8] = _letpattern5.0;
                                                        let res0: bool =
                                                            crate::cbordetver::cbor_det_serialize_map_insert(
                                                                out012,
                                                                size0,
                                                                size1
                                                            );
                                                        if res0
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
                                            match c23
                                            {
                                                option__COSE_Format_evercddl_everparsenomatch::Some
                                                { v: c14 }
                                                =>
                                                  {
                                                      let count0: u64 = (&pcount)[0];
                                                      if count0 < 18446744073709551615u64
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
                                                              let _letpattern4: (&[u8], &[u8]) =
                                                                  out.split_at(size1);
                                                              let _out01: &[u8] = _letpattern4.0;
                                                              let out2: &[u8] = _letpattern4.1;
                                                              let res2: usize =
                                                                  serialize_everparsenomatch(
                                                                      c14,
                                                                      out2
                                                                  );
                                                              if res2 > 0usize
                                                              {
                                                                  let size2: usize =
                                                                      size1.wrapping_add(res2);
                                                                  let
                                                                  _letpattern5:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size2);
                                                                  let out012: &mut [u8] =
                                                                      _letpattern5.0;
                                                                  let res0: bool =
                                                                      crate::cbordetver::cbor_det_serialize_map_insert(
                                                                          out012,
                                                                          size0,
                                                                          size1
                                                                      );
                                                                  if res0
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
                                                      { false }
                                                  },
                                                option__COSE_Format_evercddl_everparsenomatch::None
                                                => true,
                                                _ => panic!("Incomplete pattern matching")
                                            }
                                        }
                                        else
                                        { false }
                                    },
                                  either__·COSE_Format_evercddl_bstr···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·_·FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch·::Inr
                                  { v: c23 }
                                  =>
                                    {
                                        let
                                        _letpattern20:
                                        (option__COSE_Format_evercddl_everparsenomatch,
                                        option__COSE_Format_evercddl_everparsenomatch)
                                        =
                                            c23;
                                        let c12: option__COSE_Format_evercddl_everparsenomatch =
                                            _letpattern20.0;
                                        let c24: option__COSE_Format_evercddl_everparsenomatch =
                                            _letpattern20.1;
                                        let res11: bool =
                                            match c12
                                            {
                                                option__COSE_Format_evercddl_everparsenomatch::Some
                                                { v: c13 }
                                                =>
                                                  {
                                                      let count: u64 = (&pcount)[0];
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
                                                              let _letpattern4: (&[u8], &[u8]) =
                                                                  out.split_at(size1);
                                                              let _out01: &[u8] = _letpattern4.0;
                                                              let out2: &[u8] = _letpattern4.1;
                                                              let res2: usize =
                                                                  serialize_everparsenomatch(
                                                                      c13,
                                                                      out2
                                                                  );
                                                              if res2 > 0usize
                                                              {
                                                                  let size2: usize =
                                                                      size1.wrapping_add(res2);
                                                                  let
                                                                  _letpattern5:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size2);
                                                                  let out012: &mut [u8] =
                                                                      _letpattern5.0;
                                                                  let res0: bool =
                                                                      crate::cbordetver::cbor_det_serialize_map_insert(
                                                                          out012,
                                                                          size0,
                                                                          size1
                                                                      );
                                                                  if res0
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
                                                      { false }
                                                  },
                                                option__COSE_Format_evercddl_everparsenomatch::None
                                                => true,
                                                _ => panic!("Incomplete pattern matching")
                                            };
                                        if res11
                                        {
                                            match c24
                                            {
                                                option__COSE_Format_evercddl_everparsenomatch::Some
                                                { v: c13 }
                                                =>
                                                  {
                                                      let count: u64 = (&pcount)[0];
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
                                                              let _letpattern4: (&[u8], &[u8]) =
                                                                  out.split_at(size1);
                                                              let _out01: &[u8] = _letpattern4.0;
                                                              let out2: &[u8] = _letpattern4.1;
                                                              let res2: usize =
                                                                  serialize_everparsenomatch(
                                                                      c13,
                                                                      out2
                                                                  );
                                                              if res2 > 0usize
                                                              {
                                                                  let size2: usize =
                                                                      size1.wrapping_add(res2);
                                                                  let
                                                                  _letpattern5:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size2);
                                                                  let out012: &mut [u8] =
                                                                      _letpattern5.0;
                                                                  let res0: bool =
                                                                      crate::cbordetver::cbor_det_serialize_map_insert(
                                                                          out012,
                                                                          size0,
                                                                          size1
                                                                      );
                                                                  if res0
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
                                                      { false }
                                                  },
                                                option__COSE_Format_evercddl_everparsenomatch::None
                                                => true,
                                                _ => panic!("Incomplete pattern matching")
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
                    either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values::Inl
                    { v: c11 }
                    =>
                      {
                          let i: &[(evercddl_label, crate::cbordetveraux::cbor_raw)] = c11;
                          let pi: [&[(evercddl_label, crate::cbordetveraux::cbor_raw)]; 1] =
                              [i; 1usize];
                          crate::lowstar::ignore::ignore::<&[&[(evercddl_label,
                          crate::cbordetveraux::cbor_raw)]]>(&pi);
                          let mut pc: [&[(evercddl_label, crate::cbordetveraux::cbor_raw)]; 1] =
                              [i; 1usize];
                          let mut pres: [bool; 1] = [true; 1usize];
                          let res: bool = (&pres)[0];
                          let mut cond: bool =
                              if res
                              {
                                  let c3: &[(evercddl_label, crate::cbordetveraux::cbor_raw)] =
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
                                  let i1: &[(evercddl_label, crate::cbordetveraux::cbor_raw)] =
                                      (&pc)[0];
                                  let res0: (evercddl_label, crate::cbordetveraux::cbor_raw) =
                                      i1[0usize];
                                  let
                                  _letpattern10:
                                  (&[(evercddl_label, crate::cbordetveraux::cbor_raw)],
                                  &[(evercddl_label, crate::cbordetveraux::cbor_raw)])
                                  =
                                      i1.split_at(1usize);
                                  let
                                  _letpattern11: (evercddl_label, crate::cbordetveraux::cbor_raw)
                                  =
                                      {
                                          let
                                          _il: &[(evercddl_label, crate::cbordetveraux::cbor_raw)]
                                          =
                                              _letpattern10.0;
                                          let
                                          ir: &[(evercddl_label, crate::cbordetveraux::cbor_raw)]
                                          =
                                              _letpattern10.1;
                                          let
                                          i·: &[(evercddl_label, crate::cbordetveraux::cbor_raw)]
                                          =
                                              ir;
                                          (&mut pc)[0] = i·;
                                          res0
                                      };
                                  let ck: evercddl_label = _letpattern11.0;
                                  let cv: crate::cbordetveraux::cbor_raw = _letpattern11.1;
                                  let size0: usize = (&psize)[0];
                                  let _letpattern2: (&mut [u8], &mut [u8]) =
                                      out.split_at_mut(size0);
                                  let _outl1: &[u8] = _letpattern2.0;
                                  let out1: &mut [u8] = _letpattern2.1;
                                  let sz1: usize = serialize_label(ck, out1);
                                  if sz1 == 0usize
                                  { (&mut pres)[0] = false }
                                  else
                                  {
                                      let _letpattern3: (&mut [u8], &mut [u8]) =
                                          out1.split_at_mut(sz1);
                                      let outl2: &[u8] = _letpattern3.0;
                                      let out2: &mut [u8] = _letpattern3.1;
                                      let sz2: usize = serialize_values(cv, out2);
                                      if sz2 == 0usize
                                      { (&mut pres)[0] = false }
                                      else
                                      {
                                          let
                                          _letpattern4:
                                          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                          =
                                              crate::cbordetver::cbor_det_parse(outl2);
                                          match _letpattern4
                                          {
                                              crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                              { v: oo1 }
                                              =>
                                                {
                                                    let
                                                    _letpattern5:
                                                    (crate::cbordetveraux::cbor_raw, &[u8])
                                                    =
                                                        oo1;
                                                    let o1: crate::cbordetveraux::cbor_raw =
                                                        _letpattern5.0;
                                                    let _orem1: &[u8] = _letpattern5.1;
                                                    let
                                                    _letpattern6:
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                                    =
                                                        crate::cbordetver::cbor_det_parse(out2);
                                                    match _letpattern6
                                                    {
                                                        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                        { v: oo2 }
                                                        =>
                                                          {
                                                              let
                                                              _letpattern7:
                                                              (crate::cbordetveraux::cbor_raw,
                                                              &[u8])
                                                              =
                                                                  oo2;
                                                              let
                                                              o2: crate::cbordetveraux::cbor_raw
                                                              =
                                                                  _letpattern7.0;
                                                              let _orem2: &[u8] = _letpattern7.1;
                                                              let
                                                              o:
                                                              crate::cbordetveraux::cbor_map_entry
                                                              =
                                                                  crate::cbordetver::cbor_det_mk_map_entry(
                                                                      o1,
                                                                      o2
                                                                  );
                                                              let is_except: bool =
                                                                  aux_env32_map_constraint_2(o);
                                                              if is_except
                                                              { (&mut pres)[0] = false }
                                                              else
                                                              {
                                                                  let size1: usize =
                                                                      size0.wrapping_add(sz1);
                                                                  let size2: usize =
                                                                      size1.wrapping_add(sz2);
                                                                  let
                                                                  _letpattern8:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size2);
                                                                  let
                                                                  _letpattern80:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      {
                                                                          let s1: &mut [u8] =
                                                                              _letpattern8.0;
                                                                          let s2: &mut [u8] =
                                                                              _letpattern8.1;
                                                                          (s1,s2)
                                                                      };
                                                                  let outl: &mut [u8] =
                                                                      _letpattern80.0;
                                                                  let _outr: &[u8] =
                                                                      _letpattern80.1;
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
                                                          },
                                                        _ => panic!("Incomplete pattern matching")
                                                    }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          }
                                      }
                                  }
                              };
                              let res0: bool = (&pres)[0];
                              let ite: bool =
                                  if res0
                                  {
                                      let c3: &[(evercddl_label, crate::cbordetveraux::cbor_raw)] =
                                          (&pc)[0];
                                      let em: bool = c3.len() == 0usize;
                                      ! em
                                  }
                                  else
                                  { false };
                              cond = ite
                          };
                          (&pres)[0]
                      },
                    either__CDDL_Pulse_Types_slice··COSE_Format_evercddl_label···COSE_Format_evercddl_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_evercddl_label·COSE_Format_evercddl_values::Inr
                    { v: c21 }
                    =>
                      {
                          let
                          mut
                          pc:
                          [map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values;
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
                                  map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
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
                                              crate::cbordetver::cbor_det_map_iterator_is_empty(j);
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
                                              (c3.cddl_map_iterator_impl_validate_ex)(elt);
                                          if ! test_ex
                                          {
                                              let elt_value: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(elt);
                                              let test_value: bool =
                                                  (c3.cddl_map_iterator_impl_validate2)(elt_value);
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
                                  map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
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
                                  let test_key: bool = (i.cddl_map_iterator_impl_validate1)(hd_key);
                                  let mut cond0: bool =
                                      if ! test_key
                                      { true }
                                      else
                                      {
                                          let hd_value: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_value(hd);
                                          let test_value: bool =
                                              (i.cddl_map_iterator_impl_validate2)(hd_value);
                                          if ! test_value
                                          { true }
                                          else
                                          { (i.cddl_map_iterator_impl_validate_ex)(hd) }
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
                                              let hd_value: crate::cbordetveraux::cbor_raw =
                                                  crate::cbordetver::cbor_det_map_entry_value(hd2);
                                              let test_value: bool =
                                                  (i.cddl_map_iterator_impl_validate2)(hd_value);
                                              if ! test_value
                                              { true }
                                              else
                                              { (i.cddl_map_iterator_impl_validate_ex)(hd2) }
                                          };
                                      cond0 = ite
                                  };
                                  let hd1: crate::cbordetveraux::cbor_map_entry = (&phd)[0];
                                  let hd_key0: crate::cbordetveraux::cbor_raw =
                                      crate::cbordetver::cbor_det_map_entry_key(hd1);
                                  let hd_key_res: evercddl_label =
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
                                  map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
                                  =
                                      map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
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
                                  _letpattern10: (evercddl_label, crate::cbordetveraux::cbor_raw)
                                  =
                                      (hd_key_res,hd_value_res);
                                  let ck: evercddl_label = _letpattern10.0;
                                  let cv: crate::cbordetveraux::cbor_raw = _letpattern10.1;
                                  let size0: usize = (&psize)[0];
                                  let _letpattern2: (&mut [u8], &mut [u8]) =
                                      out.split_at_mut(size0);
                                  let _outl1: &[u8] = _letpattern2.0;
                                  let out1: &mut [u8] = _letpattern2.1;
                                  let sz1: usize = serialize_label(ck, out1);
                                  if sz1 == 0usize
                                  { (&mut pres)[0] = false }
                                  else
                                  {
                                      let _letpattern3: (&mut [u8], &mut [u8]) =
                                          out1.split_at_mut(sz1);
                                      let outl2: &[u8] = _letpattern3.0;
                                      let out2: &mut [u8] = _letpattern3.1;
                                      let sz2: usize = serialize_values(cv, out2);
                                      if sz2 == 0usize
                                      { (&mut pres)[0] = false }
                                      else
                                      {
                                          let
                                          _letpattern4:
                                          crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                          =
                                              crate::cbordetver::cbor_det_parse(outl2);
                                          match _letpattern4
                                          {
                                              crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                              { v: oo1 }
                                              =>
                                                {
                                                    let
                                                    _letpattern5:
                                                    (crate::cbordetveraux::cbor_raw, &[u8])
                                                    =
                                                        oo1;
                                                    let o1: crate::cbordetveraux::cbor_raw =
                                                        _letpattern5.0;
                                                    let _orem1: &[u8] = _letpattern5.1;
                                                    let
                                                    _letpattern6:
                                                    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
                                                    =
                                                        crate::cbordetver::cbor_det_parse(out2);
                                                    match _letpattern6
                                                    {
                                                        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
                                                        { v: oo2 }
                                                        =>
                                                          {
                                                              let
                                                              _letpattern7:
                                                              (crate::cbordetveraux::cbor_raw,
                                                              &[u8])
                                                              =
                                                                  oo2;
                                                              let
                                                              o2: crate::cbordetveraux::cbor_raw
                                                              =
                                                                  _letpattern7.0;
                                                              let _orem2: &[u8] = _letpattern7.1;
                                                              let
                                                              o:
                                                              crate::cbordetveraux::cbor_map_entry
                                                              =
                                                                  crate::cbordetver::cbor_det_mk_map_entry(
                                                                      o1,
                                                                      o2
                                                                  );
                                                              let is_except: bool =
                                                                  aux_env32_map_constraint_2(o);
                                                              if is_except
                                                              { (&mut pres)[0] = false }
                                                              else
                                                              {
                                                                  let size1: usize =
                                                                      size0.wrapping_add(sz1);
                                                                  let size2: usize =
                                                                      size1.wrapping_add(sz2);
                                                                  let
                                                                  _letpattern8:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      out.split_at_mut(size2);
                                                                  let
                                                                  _letpattern80:
                                                                  (&mut [u8], &mut [u8])
                                                                  =
                                                                      {
                                                                          let s1: &mut [u8] =
                                                                              _letpattern8.0;
                                                                          let s2: &mut [u8] =
                                                                              _letpattern8.1;
                                                                          (s1,s2)
                                                                      };
                                                                  let outl: &mut [u8] =
                                                                      _letpattern80.0;
                                                                  let _outr: &[u8] =
                                                                      _letpattern80.1;
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
                                                          },
                                                        _ => panic!("Incomplete pattern matching")
                                                    }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          }
                                      }
                                  }
                              };
                              let res0: bool = (&pres)[0];
                              let ite: bool =
                                  if res0
                                  {
                                      let
                                      c3:
                                      map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_evercddl_values
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
                                              crate::cbordetver::cbor_det_map_iterator_next(&mut pj);
                                          let elt_key: crate::cbordetveraux::cbor_raw =
                                              crate::cbordetver::cbor_det_map_entry_key(elt);
                                          let test_key: bool =
                                              (c3.cddl_map_iterator_impl_validate1)(elt_key);
                                          if ! ! test_key
                                          {
                                              let test_ex: bool =
                                                  (c3.cddl_map_iterator_impl_validate_ex)(elt);
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
                                          cond0 = ite
                                      };
                                      let em: bool = (&pres1)[0];
                                      ! em
                                  }
                                  else
                                  { false };
                              cond = ite
                          };
                          (&pres)[0]
                      },
                    _ => panic!("Incomplete pattern matching")
                }
            }
            else
            { false }
        };
    if res
    {
        let size: usize = (&psize)[0];
        let count: u64 = (&pcount)[0];
        crate::cbordetver::cbor_det_serialize_map(count, out, size)
    }
    else
    { 0usize }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_header_map···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_header_map <'a>, &'a [u8]) }
}

pub fn validate_and_parse_header_map <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_header_map···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_header_map···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_header_map = parse_header_map(rl);
                  option__·COSE_Format_evercddl_header_map···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_header_map···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn is_empty_iterate_array_aux_env32_type_1(
    i:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env32_type_1
) ->
    bool
{ crate::cbordetver::cbor_det_array_iterator_is_empty(i.cddl_array_iterator_contents) }

pub fn next_iterate_array_aux_env32_type_1 <'a>(
    pi:
    &'a mut
    [array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env32_type_1
    <'a>]
) ->
    evercddl_label
    <'a>
{
    let
    i:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env32_type_1
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
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env32_type_1
    =
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env32_type_1
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
    (i.cddl_array_iterator_impl_parse)(tri)
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
                      if rem.len() == 0usize { validate_header_map(res) } else { false }
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
enum evercddl_empty_or_serialized_map_ugly <'a>
{
    Inl { v: evercddl_header_map <'a> },
    Inr { v: &'a [u8] }
}

#[derive(PartialEq, Clone, Copy)]
enum evercddl_empty_or_serialized_map_tags
{
    Mkevercddl_empty_or_serialized_map0,
    Mkevercddl_empty_or_serialized_map1
}

#[derive(PartialEq, Clone, Copy)]
pub enum evercddl_empty_or_serialized_map <'a>
{
    Mkevercddl_empty_or_serialized_map0 { _x0: evercddl_header_map <'a> },
    Mkevercddl_empty_or_serialized_map1 { _x0: &'a [u8] }
}

pub fn uu___is_Mkevercddl_empty_or_serialized_map0(projectee: evercddl_empty_or_serialized_map) ->
    bool
{
    match projectee
    {
        evercddl_empty_or_serialized_map::Mkevercddl_empty_or_serialized_map0 { .. } => true,
        _ => false
    }
}

pub fn uu___is_Mkevercddl_empty_or_serialized_map1(projectee: evercddl_empty_or_serialized_map) ->
    bool
{
    match projectee
    {
        evercddl_empty_or_serialized_map::Mkevercddl_empty_or_serialized_map1 { .. } => true,
        _ => false
    }
}

fn evercddl_empty_or_serialized_map_right <'a>(x2: evercddl_empty_or_serialized_map_ugly <'a>) ->
    evercddl_empty_or_serialized_map
    <'a>
{
    match x2
    {
        evercddl_empty_or_serialized_map_ugly::Inl { v: x3 } =>
          evercddl_empty_or_serialized_map::Mkevercddl_empty_or_serialized_map0 { _x0: x3 },
        evercddl_empty_or_serialized_map_ugly::Inr { v: x4 } =>
          evercddl_empty_or_serialized_map::Mkevercddl_empty_or_serialized_map1 { _x0: x4 },
        _ => panic!("Incomplete pattern matching")
    }
}

fn evercddl_empty_or_serialized_map_left <'a>(x7: evercddl_empty_or_serialized_map <'a>) ->
    evercddl_empty_or_serialized_map_ugly
    <'a>
{
    match x7
    {
        evercddl_empty_or_serialized_map::Mkevercddl_empty_or_serialized_map0 { _x0: x10 } =>
          evercddl_empty_or_serialized_map_ugly::Inl { v: x10 },
        evercddl_empty_or_serialized_map::Mkevercddl_empty_or_serialized_map1 { _x0: x12 } =>
          evercddl_empty_or_serialized_map_ugly::Inr { v: x12 },
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
    evercddl_empty_or_serialized_map
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
                      if rem.len() == 0usize { validate_header_map(res) } else { false }
                  },
                _ => panic!("Incomplete pattern matching")
            }
        }
        else
        { false };
    let res1: evercddl_empty_or_serialized_map_ugly =
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
            let res: evercddl_header_map =
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
            evercddl_empty_or_serialized_map_ugly::Inl { v: res }
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
            evercddl_empty_or_serialized_map_ugly::Inr { v: res }
        };
    evercddl_empty_or_serialized_map_right(res1)
}

/**
Serializer for evercddl_empty_or_serialized_map
*/
pub fn
serialize_empty_or_serialized_map(c: evercddl_empty_or_serialized_map, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_empty_or_serialized_map_ugly = evercddl_empty_or_serialized_map_left(c);
    match c·
    {
        evercddl_empty_or_serialized_map_ugly::Inl { v: c1 } =>
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
        evercddl_empty_or_serialized_map_ugly::Inr { v: c2 } =>
          {
              let len: usize = c2.len();
              if (0u64 as usize) <= len && len <= 0u64 as usize
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
option__·COSE_Format_evercddl_empty_or_serialized_map···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_empty_or_serialized_map <'a>, &'a [u8]) }
}

pub fn validate_and_parse_empty_or_serialized_map <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_empty_or_serialized_map···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_empty_or_serialized_map···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_empty_or_serialized_map = parse_empty_or_serialized_map(rl);
                  option__·COSE_Format_evercddl_empty_or_serialized_map···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_empty_or_serialized_map···Pulse_Lib_Slice_slice·uint8_t·::None
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
                  crate::cbordetver::cbor_det_array_iterator_start(a),
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
                            { false }
                        }
                    }
                    else
                    { false };
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
                        validate_empty_or_serialized_map(c1)
                    };
                if test11
                {
                    let i11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                        (&pi)[0];
                    let i2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                        (&pi)[0];
                    let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
                    let test12: bool =
                        if is_done1
                        { false }
                        else
                        {
                            let c1: crate::cbordetveraux::cbor_raw =
                                crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                            validate_empty_or_serialized_map(c1)
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
                                    validate_bstr(c1)
                                };
                            if test13
                            {
                                let
                                i21:
                                crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                =
                                    (&pi)[0];
                                let is_done3: bool =
                                    crate::cbordetver::cbor_det_array_iterator_is_empty(i21);
                                if is_done3
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
                    if test120
                    { true }
                    else
                    {
                        (&mut pi)[0] = i11;
                        let
                        i20: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
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
                                validate_bstr(c1)
                            };
                        if test13
                        {
                            let
                            i21:
                            crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                            =
                                (&pi)[0];
                            let is_done3: bool =
                                crate::cbordetver::cbor_det_array_iterator_is_empty(i21);
                            if is_done3
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
                (&pi)[0];
            crate::cbordetver::cbor_det_array_iterator_is_empty(i·)
        }
        else
        { false }
    }
    else
    { false }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
either__·COSE_Format_evercddl_empty_or_serialized_map····COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr··_·COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr·
<'a>
{
    Inl { v: (evercddl_empty_or_serialized_map <'a>, (&'a [u8], &'a [u8])) },
    Inr { v: (&'a [u8], &'a [u8]) }
}

#[derive(PartialEq, Clone, Copy)]
pub struct evercddl_Sig_structure <'a>
{
    pub context: evercddl_int_ugly_tags,
    pub body_protected: evercddl_empty_or_serialized_map <'a>,
    pub _x0:
    either__·COSE_Format_evercddl_empty_or_serialized_map····COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr··_·COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr·
    <'a>
}

pub fn uu___is_Mkevercddl_Sig_structure0(projectee: evercddl_Sig_structure) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_Sig_structure>(projectee);
    true
}

fn evercddl_Sig_structure_right <'a>(
    x3:
    (evercddl_int_ugly_tags,
    (evercddl_empty_or_serialized_map
    <'a>,
    either__·COSE_Format_evercddl_empty_or_serialized_map····COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr··_·COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr·
    <'a>))
) ->
    evercddl_Sig_structure
    <'a>
{
    match x3
    { (x4,(x5,x6)) => evercddl_Sig_structure { context: x4, body_protected: x5, _x0: x6 } }
}

fn evercddl_Sig_structure_left <'a>(x7: evercddl_Sig_structure <'a>) ->
    (evercddl_int_ugly_tags,
    (evercddl_empty_or_serialized_map
    <'a>,
    either__·COSE_Format_evercddl_empty_or_serialized_map····COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr··_·COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr·
    <'a>))
{
    let x12: evercddl_int_ugly_tags = x7.context;
    let x13: evercddl_empty_or_serialized_map = x7.body_protected;
    let
    x14:
    either__·COSE_Format_evercddl_empty_or_serialized_map····COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr··_·COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr·
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
    evercddl_Sig_structure
    <'a>
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let ar: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Array { _0: a } =>
              crate::cbordetver::cbor_det_array_iterator_start(a),
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
                        { false }
                    }
                }
                else
                { false };
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
                                                            if x9 == 49u8 { true } else { false }
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
                { false }
            }
        }
        else
        { false };
    let w1: evercddl_int_ugly_tags =
        if test0 { evercddl_int_ugly_tags::Inl } else { evercddl_int_ugly_tags::Inr };
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
            validate_empty_or_serialized_map(c2)
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
    let w11: evercddl_empty_or_serialized_map = parse_empty_or_serialized_map(x0);
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
            validate_empty_or_serialized_map(c2)
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
                    validate_bstr(c2)
                };
            if test11
            {
                let i3: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pc20)[0];
                let is_done3: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i3);
                if is_done3
                { false }
                else
                {
                    let c2: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_array_iterator_next(&mut pc20);
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
    either__·COSE_Format_evercddl_empty_or_serialized_map····COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr··_·COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr·
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
                    validate_empty_or_serialized_map(c2)
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
            let w12: evercddl_empty_or_serialized_map = parse_empty_or_serialized_map(x1);
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
                    validate_bstr(c2)
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
            let w13: &[u8] = parse_bstr(x2);
            let
            mut pc50: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
            =
                [c13; 1usize];
            let x3: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc50);
            let w2: &[u8] = parse_bstr(x3);
            let w20: (&[u8], &[u8]) = (w13,w2);
            let w120: (evercddl_empty_or_serialized_map, (&[u8], &[u8])) = (w12,w20);
            either__·COSE_Format_evercddl_empty_or_serialized_map····COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr··_·COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr·::Inl
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
                    validate_bstr(c2)
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
            let w12: &[u8] = parse_bstr(x1);
            let
            mut pc40: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
            =
                [c12; 1usize];
            let x2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc40);
            let w2: &[u8] = parse_bstr(x2);
            let w20: (&[u8], &[u8]) = (w12,w2);
            either__·COSE_Format_evercddl_empty_or_serialized_map····COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr··_·COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr·::Inr
            { v: w20 }
        };
    let
    w20:
    (evercddl_empty_or_serialized_map,
    either__·COSE_Format_evercddl_empty_or_serialized_map····COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr··_·COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr·)
    =
        (w11,w2);
    let
    res1:
    (evercddl_int_ugly_tags,
    (evercddl_empty_or_serialized_map,
    either__·COSE_Format_evercddl_empty_or_serialized_map····COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr··_·COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr·))
    =
        (w1,w20);
    evercddl_Sig_structure_right(res1)
}

/**
Serializer for evercddl_Sig_structure
*/
pub fn
serialize_Sig_structure(c: evercddl_Sig_structure, out: &mut [u8]) ->
    usize
{
    let
    c·:
    (evercddl_int_ugly_tags,
    (evercddl_empty_or_serialized_map,
    either__·COSE_Format_evercddl_empty_or_serialized_map····COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr··_·COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr·))
    =
        evercddl_Sig_structure_left(c);
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let
    _letpattern:
    (evercddl_int_ugly_tags,
    (evercddl_empty_or_serialized_map,
    either__·COSE_Format_evercddl_empty_or_serialized_map····COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr··_·COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr·))
    =
        c·;
    let res: bool =
        {
            let c1: evercddl_int_ugly_tags = _letpattern.0;
            let
            c2:
            (evercddl_empty_or_serialized_map,
            either__·COSE_Format_evercddl_empty_or_serialized_map····COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr··_·COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr·)
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
                            evercddl_int_ugly_tags::Inl =>
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
                                  match res0
                                  {
                                      crate::cbordetver::option__size_t::None => 0usize,
                                      crate::cbordetver::option__size_t::Some { v: r } => r,
                                      _ => panic!("Incomplete pattern matching")
                                  }
                              },
                            evercddl_int_ugly_tags::Inr =>
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
                                  match res0
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
                (evercddl_empty_or_serialized_map,
                either__·COSE_Format_evercddl_empty_or_serialized_map····COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr··_·COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr·)
                =
                    c2;
                let c11: evercddl_empty_or_serialized_map = _letpattern1.0;
                let
                c21:
                either__·COSE_Format_evercddl_empty_or_serialized_map····COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr··_·COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr·
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
                    match c21
                    {
                        either__·COSE_Format_evercddl_empty_or_serialized_map····COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr··_·COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr·::Inl
                        { v: c12 }
                        =>
                          {
                              let _letpattern2: (evercddl_empty_or_serialized_map, (&[u8], &[u8])) =
                                  c12;
                              let c13: evercddl_empty_or_serialized_map = _letpattern2.0;
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
                                          serialize_empty_or_serialized_map(c13, out1);
                                      if size1 == 0usize
                                      { false }
                                      else
                                      {
                                          (&mut pcount)[0] = count1.wrapping_add(1u64);
                                          (&mut psize)[0] = size.wrapping_add(size1);
                                          true
                                      }
                                  }
                                  else
                                  { false };
                              if res12
                              {
                                  let _letpattern3: (&[u8], &[u8]) = c22;
                                  let c14: &[u8] = _letpattern3.0;
                                  let c23: &[u8] = _letpattern3.1;
                                  let count2: u64 = (&pcount)[0];
                                  let res13: bool =
                                      if count2 < 18446744073709551615u64
                                      {
                                          let size: usize = (&psize)[0];
                                          let _letpattern4: (&mut [u8], &mut [u8]) =
                                              out.split_at_mut(size);
                                          let _out0: &[u8] = _letpattern4.0;
                                          let out1: &mut [u8] = _letpattern4.1;
                                          let size1: usize = serialize_bstr(c14, out1);
                                          if size1 == 0usize
                                          { false }
                                          else
                                          {
                                              (&mut pcount)[0] = count2.wrapping_add(1u64);
                                              (&mut psize)[0] = size.wrapping_add(size1);
                                              true
                                          }
                                      }
                                      else
                                      { false };
                                  if res13
                                  {
                                      let count3: u64 = (&pcount)[0];
                                      if count3 < 18446744073709551615u64
                                      {
                                          let size: usize = (&psize)[0];
                                          let _letpattern4: (&mut [u8], &mut [u8]) =
                                              out.split_at_mut(size);
                                          let _out0: &[u8] = _letpattern4.0;
                                          let out1: &mut [u8] = _letpattern4.1;
                                          let size1: usize = serialize_bstr(c23, out1);
                                          if size1 == 0usize
                                          { false }
                                          else
                                          {
                                              (&mut pcount)[0] = count3.wrapping_add(1u64);
                                              (&mut psize)[0] = size.wrapping_add(size1);
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
                        either__·COSE_Format_evercddl_empty_or_serialized_map····COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr··_·COSE_Format_evercddl_bstr···COSE_Format_evercddl_bstr·::Inr
                        { v: c22 }
                        =>
                          {
                              let _letpattern2: (&[u8], &[u8]) = c22;
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
                                      let size1: usize = serialize_bstr(c12, out1);
                                      if size1 == 0usize
                                      { false }
                                      else
                                      {
                                          (&mut pcount)[0] = count1.wrapping_add(1u64);
                                          (&mut psize)[0] = size.wrapping_add(size1);
                                          true
                                      }
                                  }
                                  else
                                  { false };
                              if res12
                              {
                                  let count2: u64 = (&pcount)[0];
                                  if count2 < 18446744073709551615u64
                                  {
                                      let size: usize = (&psize)[0];
                                      let _letpattern3: (&mut [u8], &mut [u8]) =
                                          out.split_at_mut(size);
                                      let _out0: &[u8] = _letpattern3.0;
                                      let out1: &mut [u8] = _letpattern3.1;
                                      let size1: usize = serialize_bstr(c23, out1);
                                      if size1 == 0usize
                                      { false }
                                      else
                                      {
                                          (&mut pcount)[0] = count2.wrapping_add(1u64);
                                          (&mut psize)[0] = size.wrapping_add(size1);
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
        let size: usize = (&psize)[0];
        let count: u64 = (&pcount)[0];
        crate::cbordetver::cbor_det_serialize_array(count, out, size)
    }
    else
    { 0usize }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_Sig_structure···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_Sig_structure <'a>, &'a [u8]) }
}

pub fn validate_and_parse_Sig_structure <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_Sig_structure···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_Sig_structure···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_Sig_structure = parse_Sig_structure(rl);
                  option__·COSE_Format_evercddl_Sig_structure···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_Sig_structure···Pulse_Lib_Slice_slice·uint8_t·::None
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
                  crate::cbordetver::cbor_det_array_iterator_start(a),
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
                validate_empty_or_serialized_map(c1)
            };
        let test10: bool =
            if test1
            {
                let i10: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0];
                let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i10);
                if is_done0
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
                        if test { true } else { validate_nil(c1) }
                    };
                if test11
                {
                    let i11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                        (&pi)[0];
                    let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i11);
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
                { false }
            }
            else
            { false };
        if b_success
        {
            let i·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pi)[0];
            crate::cbordetver::cbor_det_array_iterator_is_empty(i·)
        }
        else
        { false }
    }
    else
    { false }
}

#[derive(PartialEq, Clone, Copy)]
pub enum either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil <'a>
{
    Inl { v: &'a [u8] },
    Inr { v: evercddl_nil }
}

#[derive(PartialEq, Clone, Copy)]
pub struct evercddl_COSE_Sign1 <'a>
{
    pub protected: evercddl_empty_or_serialized_map <'a>,
    pub unprotected: evercddl_header_map <'a>,
    pub payload: either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil <'a>,
    pub signature: &'a [u8]
}

pub fn uu___is_Mkevercddl_COSE_Sign10(projectee: evercddl_COSE_Sign1) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_COSE_Sign1>(projectee);
    true
}

fn evercddl_COSE_Sign1_right <'a>(
    x4:
    ((evercddl_empty_or_serialized_map <'a>, evercddl_header_map <'a>),
    (either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil <'a>, &'a [u8]))
) ->
    evercddl_COSE_Sign1
    <'a>
{
    match x4
    {
        ((x5,x6),(x7,x8)) =>
          evercddl_COSE_Sign1 { protected: x5, unprotected: x6, payload: x7, signature: x8 }
    }
}

fn evercddl_COSE_Sign1_left <'a>(x9: evercddl_COSE_Sign1 <'a>) ->
    ((evercddl_empty_or_serialized_map <'a>, evercddl_header_map <'a>),
    (either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil <'a>, &'a [u8]))
{
    let x15: evercddl_empty_or_serialized_map = x9.protected;
    let x16: evercddl_header_map = x9.unprotected;
    let x17: either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil = x9.payload;
    let x18: &[u8] = x9.signature;
    ((x15,x16),(x17,x18))
}

/**
Parser for evercddl_COSE_Sign1
*/
pub fn
parse_COSE_Sign1
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_COSE_Sign1
    <'a>
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let ar: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Array { _0: a } =>
              crate::cbordetver::cbor_det_array_iterator_start(a),
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
            validate_empty_or_serialized_map(c1)
        };
    let _tmp: bool =
        if test1
        {
            let i0: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc)[0];
            let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i0);
            if is_done0
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
            validate_empty_or_serialized_map(c2)
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
    let w1: evercddl_empty_or_serialized_map = parse_empty_or_serialized_map(x);
    let mut pc20: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c11; 1usize];
    let x0: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc20);
    let w2: evercddl_header_map = parse_header_map(x0);
    let w10: (evercddl_empty_or_serialized_map, evercddl_header_map) = (w1,w2);
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
            if test { true } else { validate_nil(c2) }
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
    let w11: either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil =
        if test
        {
            let res: &[u8] = parse_bstr(x1);
            either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil::Inl { v: res }
        }
        else
        {
            let res: evercddl_nil = parse_nil(x1);
            either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil::Inr { v: res }
        };
    let mut pc22: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c110; 1usize];
    let x2: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc22);
    let w20: &[u8] = parse_bstr(x2);
    let w21: (either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil, &[u8]) = (w11,w20);
    let
    res1:
    ((evercddl_empty_or_serialized_map, evercddl_header_map),
    (either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil, &[u8]))
    =
        (w10,w21);
    evercddl_COSE_Sign1_right(res1)
}

/**
Serializer for evercddl_COSE_Sign1
*/
pub fn
serialize_COSE_Sign1(c: evercddl_COSE_Sign1, out: &mut [u8]) ->
    usize
{
    let
    c·:
    ((evercddl_empty_or_serialized_map, evercddl_header_map),
    (either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil, &[u8]))
    =
        evercddl_COSE_Sign1_left(c);
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let
    _letpattern:
    ((evercddl_empty_or_serialized_map, evercddl_header_map),
    (either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil, &[u8]))
    =
        c·;
    let res: bool =
        {
            let c1: (evercddl_empty_or_serialized_map, evercddl_header_map) = _letpattern.0;
            let c2: (either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil, &[u8]) =
                _letpattern.1;
            let _letpattern1: (evercddl_empty_or_serialized_map, evercddl_header_map) = c1;
            let res1: bool =
                {
                    let c11: evercddl_empty_or_serialized_map = _letpattern1.0;
                    let c21: evercddl_header_map = _letpattern1.1;
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
                        { false }
                    }
                    else
                    { false }
                };
            if res1
            {
                let
                _letpattern10: (either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil, &[u8])
                =
                    c2;
                let c11: either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil =
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
                                either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil::Inl
                                { v: c12 }
                                => serialize_bstr(c12, out1),
                                either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil::Inr
                                { v: c22 }
                                => serialize_nil(c22, out1),
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
                    if count0 < 18446744073709551615u64
                    {
                        let size: usize = (&psize)[0];
                        let _letpattern2: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
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
        let size: usize = (&psize)[0];
        let count: u64 = (&pcount)[0];
        crate::cbordetver::cbor_det_serialize_array(count, out, size)
    }
    else
    { 0usize }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_COSE_Sign1···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_COSE_Sign1 <'a>, &'a [u8]) }
}

pub fn validate_and_parse_COSE_Sign1 <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_COSE_Sign1···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_COSE_Sign1···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_COSE_Sign1 = parse_COSE_Sign1(rl);
                  option__·COSE_Format_evercddl_COSE_Sign1···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_COSE_Sign1···Pulse_Lib_Slice_slice·uint8_t·::None
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
            validate_COSE_Sign1(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_COSE_Sign1_Tagged <'a> = evercddl_COSE_Sign1 <'a>;

pub fn uu___is_Mkevercddl_COSE_Sign1_Tagged0(projectee: evercddl_COSE_Sign1) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_COSE_Sign1>(projectee);
    true
}

fn evercddl_COSE_Sign1_Tagged_right <'a>(x1: evercddl_COSE_Sign1 <'a>) ->
    evercddl_COSE_Sign1
    <'a>
{ x1 }

fn evercddl_COSE_Sign1_Tagged_left <'a>(x3: evercddl_COSE_Sign1 <'a>) ->
    evercddl_COSE_Sign1
    <'a>
{ x3 }

/**
Parser for evercddl_COSE_Sign1_Tagged
*/
pub fn
parse_COSE_Sign1_Tagged
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_COSE_Sign1
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
    let res1: evercddl_COSE_Sign1 = parse_COSE_Sign1(cpl);
    evercddl_COSE_Sign1_Tagged_right(res1)
}

/**
Serializer for evercddl_COSE_Sign1_Tagged
*/
pub fn
serialize_COSE_Sign1_Tagged(c: evercddl_COSE_Sign1, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_COSE_Sign1 = evercddl_COSE_Sign1_Tagged_left(c);
    let c·1: (u64, evercddl_COSE_Sign1) = (18u64,c·);
    let _letpattern: (u64, evercddl_COSE_Sign1) = c·1;
    let ctag: u64 = _letpattern.0;
    let cpayload: evercddl_COSE_Sign1 = _letpattern.1;
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
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_COSE_Sign1_Tagged···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_COSE_Sign1 <'a>, &'a [u8]) }
}

pub fn validate_and_parse_COSE_Sign1_Tagged <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_COSE_Sign1_Tagged···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_COSE_Sign1_Tagged···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_COSE_Sign1 = parse_COSE_Sign1_Tagged(rl);
                  option__·COSE_Format_evercddl_COSE_Sign1_Tagged···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_COSE_Sign1_Tagged···Pulse_Lib_Slice_slice·uint8_t·::None
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
                  crate::cbordetver::cbor_det_array_iterator_start(a),
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
                validate_empty_or_serialized_map(c1)
            };
        let test10: bool =
            if test1
            {
                let i10: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0];
                let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i10);
                if is_done0
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
            if test10
            {
                let i10: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0];
                let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i10);
                if is_done0
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
                (&pi)[0];
            crate::cbordetver::cbor_det_array_iterator_is_empty(i·)
        }
        else
        { false }
    }
    else
    { false }
}

#[derive(PartialEq, Clone, Copy)]
pub struct evercddl_COSE_Signature <'a>
{
    pub protected: evercddl_empty_or_serialized_map <'a>,
    pub unprotected: evercddl_header_map <'a>,
    pub signature: &'a [u8]
}

pub fn uu___is_Mkevercddl_COSE_Signature0(projectee: evercddl_COSE_Signature) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_COSE_Signature>(projectee);
    true
}

fn evercddl_COSE_Signature_right <'a>(
    x3: ((evercddl_empty_or_serialized_map <'a>, evercddl_header_map <'a>), &'a [u8])
) ->
    evercddl_COSE_Signature
    <'a>
{
    match x3
    { ((x4,x5),x6) => evercddl_COSE_Signature { protected: x4, unprotected: x5, signature: x6 } }
}

fn evercddl_COSE_Signature_left <'a>(x7: evercddl_COSE_Signature <'a>) ->
    ((evercddl_empty_or_serialized_map <'a>, evercddl_header_map <'a>), &'a [u8])
{
    let x12: evercddl_empty_or_serialized_map = x7.protected;
    let x13: evercddl_header_map = x7.unprotected;
    let x14: &[u8] = x7.signature;
    ((x12,x13),x14)
}

/**
Parser for evercddl_COSE_Signature
*/
pub fn
parse_COSE_Signature
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_COSE_Signature
    <'a>
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let ar: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Array { _0: a } =>
              crate::cbordetver::cbor_det_array_iterator_start(a),
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
            validate_empty_or_serialized_map(c1)
        };
    let _tmp: bool =
        if test1
        {
            let i0: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc)[0];
            let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i0);
            if is_done0
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
            validate_empty_or_serialized_map(c2)
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
    let w1: evercddl_empty_or_serialized_map = parse_empty_or_serialized_map(x);
    let mut pc20: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c11; 1usize];
    let x0: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc20);
    let w2: evercddl_header_map = parse_header_map(x0);
    let w10: (evercddl_empty_or_serialized_map, evercddl_header_map) = (w1,w2);
    let mut pc10: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c1; 1usize];
    let x1: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc10);
    let w20: &[u8] = parse_bstr(x1);
    let res1: ((evercddl_empty_or_serialized_map, evercddl_header_map), &[u8]) = (w10,w20);
    evercddl_COSE_Signature_right(res1)
}

/**
Serializer for evercddl_COSE_Signature
*/
pub fn
serialize_COSE_Signature(c: evercddl_COSE_Signature, out: &mut [u8]) ->
    usize
{
    let c·: ((evercddl_empty_or_serialized_map, evercddl_header_map), &[u8]) =
        evercddl_COSE_Signature_left(c);
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let _letpattern: ((evercddl_empty_or_serialized_map, evercddl_header_map), &[u8]) = c·;
    let res: bool =
        {
            let c1: (evercddl_empty_or_serialized_map, evercddl_header_map) = _letpattern.0;
            let c2: &[u8] = _letpattern.1;
            let _letpattern1: (evercddl_empty_or_serialized_map, evercddl_header_map) = c1;
            let res1: bool =
                {
                    let c11: evercddl_empty_or_serialized_map = _letpattern1.0;
                    let c21: evercddl_header_map = _letpattern1.1;
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
                        { false }
                    }
                    else
                    { false }
                };
            if res1
            {
                let count: u64 = (&pcount)[0];
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
                { false }
            }
            else
            { false }
        };
    if res
    {
        let size: usize = (&psize)[0];
        let count: u64 = (&pcount)[0];
        crate::cbordetver::cbor_det_serialize_array(count, out, size)
    }
    else
    { 0usize }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_COSE_Signature···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_COSE_Signature <'a>, &'a [u8]) }
}

pub fn validate_and_parse_COSE_Signature <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_COSE_Signature···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_COSE_Signature···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_COSE_Signature = parse_COSE_Signature(rl);
                  option__·COSE_Format_evercddl_COSE_Signature···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_COSE_Signature···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn aux_env39_validate_1(
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
        validate_COSE_Signature(c)
    }
}

pub type aux_env39_type_1 <'a> = evercddl_COSE_Signature <'a>;

pub fn uu___is_Mkaux_env39_type_10(projectee: evercddl_COSE_Signature) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_COSE_Signature>(projectee);
    true
}

fn aux_env39_type_1_right <'a>(x1: evercddl_COSE_Signature <'a>) ->
    evercddl_COSE_Signature
    <'a>
{ x1 }

fn aux_env39_type_1_left <'a>(x3: evercddl_COSE_Signature <'a>) -> evercddl_COSE_Signature <'a>
{ x3 }

/**
Parser for aux_env39_type_1
*/
pub fn
aux_env39_parse_1
<'a>(c: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>) ->
    evercddl_COSE_Signature
    <'a>
{
    let mut pc: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c; 1usize];
    let x: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
    let res1: evercddl_COSE_Signature = parse_COSE_Signature(x);
    aux_env39_type_1_right(res1)
}

/**
Serializer for aux_env39_type_1
*/
pub fn
aux_env39_serialize_1(
    c: evercddl_COSE_Signature,
    out: &mut [u8],
    out_count: &mut [u64],
    out_size: &mut [usize]
) ->
    bool
{
    let c·: evercddl_COSE_Signature = aux_env39_type_1_left(c);
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
                  crate::cbordetver::cbor_det_array_iterator_start(a),
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
                validate_empty_or_serialized_map(c1)
            };
        let test10: bool =
            if test1
            {
                let i10: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0];
                let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i10);
                if is_done0
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
                        if test { true } else { validate_nil(c1) }
                    };
                if test11
                {
                    let i11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                        (&pi)[0];
                    let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i11);
                    if is_done1
                    { false }
                    else
                    {
                        let c1: crate::cbordetveraux::cbor_raw =
                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                        let ty1: u8 = crate::cbordetver::cbor_det_major_type(c1);
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
                                      crate::cbordetver::cbor_det_array_iterator_start(a),
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
                                        crate::cbordetver::cbor_det_array_iterator_next(&mut pi1);
                                    validate_COSE_Signature(c2)
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
                                            crate::cbordetver::cbor_det_array_iterator_is_empty(i30);
                                        let cont: bool =
                                            if is_done11
                                            { false }
                                            else
                                            {
                                                let c2: crate::cbordetveraux::cbor_raw =
                                                    crate::cbordetver::cbor_det_array_iterator_next(
                                                        &mut pi1
                                                    );
                                                validate_COSE_Signature(c2)
                                            };
                                        if ! cont
                                        {
                                            (&mut pi1)[0] = i110;
                                            (&mut pcont)[0] = false
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
                                    (&pi1)[0];
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
                (&pi)[0];
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
array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env39_type_1
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
    evercddl_COSE_Signature
    <'a1>
}

#[derive(PartialEq, Clone, Copy)]
pub enum
either__CDDL_Pulse_Types_slice·COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env39_type_1
<'a>
{
    Inl { v: &'a [evercddl_COSE_Signature <'a>] },
    Inr
    {
        v:
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env39_type_1
        <'a>
    }
}

#[derive(PartialEq, Clone, Copy)]
pub struct evercddl_COSE_Sign <'a>
{
    pub protected: evercddl_empty_or_serialized_map <'a>,
    pub unprotected: evercddl_header_map <'a>,
    pub payload: either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil <'a>,
    pub signatures:
    either__CDDL_Pulse_Types_slice·COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env39_type_1
    <'a>
}

pub fn uu___is_Mkevercddl_COSE_Sign0(projectee: evercddl_COSE_Sign) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_COSE_Sign>(projectee);
    true
}

fn evercddl_COSE_Sign_right <'a>(
    x4:
    ((evercddl_empty_or_serialized_map <'a>, evercddl_header_map <'a>),
    (either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil
    <'a>,
    either__CDDL_Pulse_Types_slice·COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env39_type_1
    <'a>))
) ->
    evercddl_COSE_Sign
    <'a>
{
    match x4
    {
        ((x5,x6),(x7,x8)) =>
          evercddl_COSE_Sign { protected: x5, unprotected: x6, payload: x7, signatures: x8 }
    }
}

fn evercddl_COSE_Sign_left <'a>(x9: evercddl_COSE_Sign <'a>) ->
    ((evercddl_empty_or_serialized_map <'a>, evercddl_header_map <'a>),
    (either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil
    <'a>,
    either__CDDL_Pulse_Types_slice·COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env39_type_1
    <'a>))
{
    let x15: evercddl_empty_or_serialized_map = x9.protected;
    let x16: evercddl_header_map = x9.unprotected;
    let x17: either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil = x9.payload;
    let
    x18:
    either__CDDL_Pulse_Types_slice·COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env39_type_1
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
    evercddl_COSE_Sign
    <'a>
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let ar: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Array { _0: a } =>
              crate::cbordetver::cbor_det_array_iterator_start(a),
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
            validate_empty_or_serialized_map(c1)
        };
    let _tmp: bool =
        if test1
        {
            let i0: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pc)[0];
            let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i0);
            if is_done0
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
            validate_empty_or_serialized_map(c2)
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
    let w1: evercddl_empty_or_serialized_map = parse_empty_or_serialized_map(x);
    let mut pc20: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c11; 1usize];
    let x0: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc20);
    let w2: evercddl_header_map = parse_header_map(x0);
    let w10: (evercddl_empty_or_serialized_map, evercddl_header_map) = (w1,w2);
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
            if test { true } else { validate_nil(c2) }
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
    let w11: either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil =
        if test
        {
            let res: &[u8] = parse_bstr(x1);
            either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil::Inl { v: res }
        }
        else
        {
            let res: evercddl_nil = parse_nil(x1);
            either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil::Inr { v: res }
        };
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
              crate::cbordetver::cbor_det_array_iterator_start(a),
            _ => panic!("Incomplete pattern matching")
        };
    let
    i2:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env39_type_1
    =
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env39_type_1
        {
            cddl_array_iterator_contents: ar1,
            cddl_array_iterator_impl_validate: aux_env39_validate_1,
            cddl_array_iterator_impl_parse: aux_env39_parse_1
        };
    let
    w20:
    either__CDDL_Pulse_Types_slice·COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env39_type_1
    =
        either__CDDL_Pulse_Types_slice·COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env39_type_1::Inr
        { v: i2 };
    let
    w21:
    (either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil,
    either__CDDL_Pulse_Types_slice·COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env39_type_1)
    =
        (w11,w20);
    let
    res1:
    ((evercddl_empty_or_serialized_map, evercddl_header_map),
    (either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil,
    either__CDDL_Pulse_Types_slice·COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env39_type_1))
    =
        (w10,w21);
    evercddl_COSE_Sign_right(res1)
}

/**
Serializer for evercddl_COSE_Sign
*/
pub fn
serialize_COSE_Sign(c: evercddl_COSE_Sign, out: &mut [u8]) ->
    usize
{
    let
    c·:
    ((evercddl_empty_or_serialized_map, evercddl_header_map),
    (either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil,
    either__CDDL_Pulse_Types_slice·COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env39_type_1))
    =
        evercddl_COSE_Sign_left(c);
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let
    _letpattern:
    ((evercddl_empty_or_serialized_map, evercddl_header_map),
    (either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil,
    either__CDDL_Pulse_Types_slice·COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env39_type_1))
    =
        c·;
    let res: bool =
        {
            let c1: (evercddl_empty_or_serialized_map, evercddl_header_map) = _letpattern.0;
            let
            c2:
            (either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil,
            either__CDDL_Pulse_Types_slice·COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env39_type_1)
            =
                _letpattern.1;
            let _letpattern1: (evercddl_empty_or_serialized_map, evercddl_header_map) = c1;
            let res1: bool =
                {
                    let c11: evercddl_empty_or_serialized_map = _letpattern1.0;
                    let c21: evercddl_header_map = _letpattern1.1;
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
                        { false }
                    }
                    else
                    { false }
                };
            if res1
            {
                let
                _letpattern10:
                (either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil,
                either__CDDL_Pulse_Types_slice·COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env39_type_1)
                =
                    c2;
                let c11: either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil =
                    _letpattern10.0;
                let
                c21:
                either__CDDL_Pulse_Types_slice·COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env39_type_1
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
                                either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil::Inl
                                { v: c12 }
                                => serialize_bstr(c12, out1),
                                either__COSE_Format_evercddl_bstr_COSE_Format_evercddl_nil::Inr
                                { v: c22 }
                                => serialize_nil(c22, out1),
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
                    if count0 < 18446744073709551615u64
                    {
                        let size: usize = (&psize)[0];
                        let _letpattern2: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                        let _out0: &[u8] = _letpattern2.0;
                        let out1: &mut [u8] = _letpattern2.1;
                        let mut pcount1: [u64; 1] = [0u64; 1usize];
                        let mut psize1: [usize; 1] = [0usize; 1usize];
                        let res: bool =
                            match c21
                            {
                                either__CDDL_Pulse_Types_slice·COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env39_type_1::Inl
                                { v: c12 }
                                =>
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
                                          let x: evercddl_COSE_Signature = c12[i];
                                          let res0: bool =
                                              aux_env39_serialize_1(
                                                  x,
                                                  out1,
                                                  &mut pcount1,
                                                  &mut psize1
                                              );
                                          if res0
                                          {
                                              let i·: usize = i.wrapping_add(1usize);
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
                                  },
                                either__CDDL_Pulse_Types_slice·COSE_Format_aux_env39_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env39_type_1::Inr
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
                                          [array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env39_type_1;
                                          1]
                                          =
                                              [c22; 1usize];
                                          let mut pres: [bool; 1] = [true; 1usize];
                                          let res: bool = (&pres)[0];
                                          let mut cond: bool =
                                              if res
                                              {
                                                  let
                                                  c3:
                                                  array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env39_type_1
                                                  =
                                                      (&pc)[0];
                                                  let em1: bool =
                                                      crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                          c3.cddl_array_iterator_contents
                                                      );
                                                  ! em1
                                              }
                                              else
                                              { false };
                                          while
                                          cond
                                          {
                                              let
                                              i:
                                              array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env39_type_1
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
                                                  [i.cddl_array_iterator_contents; 1usize];
                                              let _test: bool =
                                                  (i.cddl_array_iterator_impl_validate)(&mut pj);
                                              crate::lowstar::ignore::ignore::<bool>(_test);
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
                                              array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env39_type_1
                                              =
                                                  array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env39_type_1
                                                  {
                                                      cddl_array_iterator_contents: ji,
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
                                              let x: evercddl_COSE_Signature =
                                                  (i.cddl_array_iterator_impl_parse)(tri);
                                              let res0: bool =
                                                  aux_env39_serialize_1(
                                                      x,
                                                      out1,
                                                      &mut pcount1,
                                                      &mut psize1
                                                  );
                                              if ! res0 { (&mut pres)[0] = false };
                                              let res2: bool = (&pres)[0];
                                              let ite: bool =
                                                  if res2
                                                  {
                                                      let
                                                      c3:
                                                      array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env39_type_1
                                                      =
                                                          (&pc)[0];
                                                      let em1: bool =
                                                          crate::cbordetver::cbor_det_array_iterator_is_empty(
                                                              c3.cddl_array_iterator_contents
                                                          );
                                                      ! em1
                                                  }
                                                  else
                                                  { false };
                                              cond = ite
                                          };
                                          (&pres)[0]
                                      }
                                  },
                                _ => panic!("Incomplete pattern matching")
                            };
                        let size1: usize =
                            if res
                            {
                                let size1: usize = (&psize1)[0];
                                let count1: u64 = (&pcount1)[0];
                                crate::cbordetver::cbor_det_serialize_array(count1, out1, size1)
                            }
                            else
                            { 0usize };
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
        let size: usize = (&psize)[0];
        let count: u64 = (&pcount)[0];
        crate::cbordetver::cbor_det_serialize_array(count, out, size)
    }
    else
    { 0usize }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_COSE_Sign···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_COSE_Sign <'a>, &'a [u8]) }
}

pub fn validate_and_parse_COSE_Sign <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_COSE_Sign···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_COSE_Sign···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_COSE_Sign = parse_COSE_Sign(rl);
                  option__·COSE_Format_evercddl_COSE_Sign···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_COSE_Sign···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn is_empty_iterate_array_aux_env39_type_1(
    i:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env39_type_1
) ->
    bool
{ crate::cbordetver::cbor_det_array_iterator_is_empty(i.cddl_array_iterator_contents) }

pub fn next_iterate_array_aux_env39_type_1 <'a>(
    pi:
    &'a mut
    [array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env39_type_1
    <'a>]
) ->
    evercddl_COSE_Signature
    <'a>
{
    let
    i:
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env39_type_1
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
    array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env39_type_1
    =
        array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env39_type_1
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
    (i.cddl_array_iterator_impl_parse)(tri)
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
            validate_COSE_Sign(c·)
        }
        else
        { false }
    }
    else
    { false }
}

pub type evercddl_COSE_Sign_Tagged <'a> = evercddl_COSE_Sign <'a>;

pub fn uu___is_Mkevercddl_COSE_Sign_Tagged0(projectee: evercddl_COSE_Sign) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_COSE_Sign>(projectee);
    true
}

fn evercddl_COSE_Sign_Tagged_right <'a>(x1: evercddl_COSE_Sign <'a>) -> evercddl_COSE_Sign <'a>
{ x1 }

fn evercddl_COSE_Sign_Tagged_left <'a>(x3: evercddl_COSE_Sign <'a>) -> evercddl_COSE_Sign <'a>
{ x3 }

/**
Parser for evercddl_COSE_Sign_Tagged
*/
pub fn
parse_COSE_Sign_Tagged
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_COSE_Sign
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
    let res1: evercddl_COSE_Sign = parse_COSE_Sign(cpl);
    evercddl_COSE_Sign_Tagged_right(res1)
}

/**
Serializer for evercddl_COSE_Sign_Tagged
*/
pub fn
serialize_COSE_Sign_Tagged(c: evercddl_COSE_Sign, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_COSE_Sign = evercddl_COSE_Sign_Tagged_left(c);
    let c·1: (u64, evercddl_COSE_Sign) = (98u64,c·);
    let _letpattern: (u64, evercddl_COSE_Sign) = c·1;
    let ctag: u64 = _letpattern.0;
    let cpayload: evercddl_COSE_Sign = _letpattern.1;
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
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_COSE_Sign_Tagged···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_COSE_Sign <'a>, &'a [u8]) }
}

pub fn validate_and_parse_COSE_Sign_Tagged <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_COSE_Sign_Tagged···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_COSE_Sign_Tagged···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_COSE_Sign = parse_COSE_Sign_Tagged(rl);
                  option__·COSE_Format_evercddl_COSE_Sign_Tagged···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_COSE_Sign_Tagged···Pulse_Lib_Slice_slice·uint8_t·::None
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
enum evercddl_COSE_Tagged_Message_ugly <'a>
{
    Inl { v: evercddl_COSE_Sign <'a> },
    Inr { v: evercddl_COSE_Sign1 <'a> }
}

#[derive(PartialEq, Clone, Copy)]
enum evercddl_COSE_Tagged_Message_tags
{
    Mkevercddl_COSE_Tagged_Message0,
    Mkevercddl_COSE_Tagged_Message1
}

#[derive(PartialEq, Clone, Copy)]
pub enum evercddl_COSE_Tagged_Message <'a>
{
    Mkevercddl_COSE_Tagged_Message0 { _x0: evercddl_COSE_Sign <'a> },
    Mkevercddl_COSE_Tagged_Message1 { _x0: evercddl_COSE_Sign1 <'a> }
}

pub fn uu___is_Mkevercddl_COSE_Tagged_Message0(projectee: evercddl_COSE_Tagged_Message) -> bool
{
    match projectee
    { evercddl_COSE_Tagged_Message::Mkevercddl_COSE_Tagged_Message0 { .. } => true, _ => false }
}

pub fn uu___is_Mkevercddl_COSE_Tagged_Message1(projectee: evercddl_COSE_Tagged_Message) -> bool
{
    match projectee
    { evercddl_COSE_Tagged_Message::Mkevercddl_COSE_Tagged_Message1 { .. } => true, _ => false }
}

fn evercddl_COSE_Tagged_Message_right <'a>(x2: evercddl_COSE_Tagged_Message_ugly <'a>) ->
    evercddl_COSE_Tagged_Message
    <'a>
{
    match x2
    {
        evercddl_COSE_Tagged_Message_ugly::Inl { v: x3 } =>
          evercddl_COSE_Tagged_Message::Mkevercddl_COSE_Tagged_Message0 { _x0: x3 },
        evercddl_COSE_Tagged_Message_ugly::Inr { v: x4 } =>
          evercddl_COSE_Tagged_Message::Mkevercddl_COSE_Tagged_Message1 { _x0: x4 },
        _ => panic!("Incomplete pattern matching")
    }
}

fn evercddl_COSE_Tagged_Message_left <'a>(x7: evercddl_COSE_Tagged_Message <'a>) ->
    evercddl_COSE_Tagged_Message_ugly
    <'a>
{
    match x7
    {
        evercddl_COSE_Tagged_Message::Mkevercddl_COSE_Tagged_Message0 { _x0: x10 } =>
          evercddl_COSE_Tagged_Message_ugly::Inl { v: x10 },
        evercddl_COSE_Tagged_Message::Mkevercddl_COSE_Tagged_Message1 { _x0: x12 } =>
          evercddl_COSE_Tagged_Message_ugly::Inr { v: x12 },
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Parser for evercddl_COSE_Tagged_Message
*/
pub fn
parse_COSE_Tagged_Message
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_COSE_Tagged_Message
    <'a>
{
    let test: bool = validate_COSE_Sign_Tagged(c);
    let res1: evercddl_COSE_Tagged_Message_ugly =
        if test
        {
            let res: evercddl_COSE_Sign = parse_COSE_Sign_Tagged(c);
            evercddl_COSE_Tagged_Message_ugly::Inl { v: res }
        }
        else
        {
            let res: evercddl_COSE_Sign1 = parse_COSE_Sign1_Tagged(c);
            evercddl_COSE_Tagged_Message_ugly::Inr { v: res }
        };
    evercddl_COSE_Tagged_Message_right(res1)
}

/**
Serializer for evercddl_COSE_Tagged_Message
*/
pub fn
serialize_COSE_Tagged_Message(c: evercddl_COSE_Tagged_Message, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_COSE_Tagged_Message_ugly = evercddl_COSE_Tagged_Message_left(c);
    match c·
    {
        evercddl_COSE_Tagged_Message_ugly::Inl { v: c1 } => serialize_COSE_Sign_Tagged(c1, out),
        evercddl_COSE_Tagged_Message_ugly::Inr { v: c2 } => serialize_COSE_Sign1_Tagged(c2, out),
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_COSE_Tagged_Message···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_COSE_Tagged_Message <'a>, &'a [u8]) }
}

pub fn validate_and_parse_COSE_Tagged_Message <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_COSE_Tagged_Message···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_COSE_Tagged_Message···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_COSE_Tagged_Message = parse_COSE_Tagged_Message(rl);
                  option__·COSE_Format_evercddl_COSE_Tagged_Message···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_COSE_Tagged_Message···Pulse_Lib_Slice_slice·uint8_t·::None
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
enum evercddl_COSE_Untagged_Message_ugly <'a>
{
    Inl { v: evercddl_COSE_Sign <'a> },
    Inr { v: evercddl_COSE_Sign1 <'a> }
}

#[derive(PartialEq, Clone, Copy)]
enum evercddl_COSE_Untagged_Message_tags
{
    Mkevercddl_COSE_Untagged_Message0,
    Mkevercddl_COSE_Untagged_Message1
}

#[derive(PartialEq, Clone, Copy)]
pub enum evercddl_COSE_Untagged_Message <'a>
{
    Mkevercddl_COSE_Untagged_Message0 { _x0: evercddl_COSE_Sign <'a> },
    Mkevercddl_COSE_Untagged_Message1 { _x0: evercddl_COSE_Sign1 <'a> }
}

pub fn uu___is_Mkevercddl_COSE_Untagged_Message0(projectee: evercddl_COSE_Untagged_Message) ->
    bool
{
    match projectee
    {
        evercddl_COSE_Untagged_Message::Mkevercddl_COSE_Untagged_Message0 { .. } => true,
        _ => false
    }
}

pub fn uu___is_Mkevercddl_COSE_Untagged_Message1(projectee: evercddl_COSE_Untagged_Message) ->
    bool
{
    match projectee
    {
        evercddl_COSE_Untagged_Message::Mkevercddl_COSE_Untagged_Message1 { .. } => true,
        _ => false
    }
}

fn evercddl_COSE_Untagged_Message_right <'a>(x2: evercddl_COSE_Untagged_Message_ugly <'a>) ->
    evercddl_COSE_Untagged_Message
    <'a>
{
    match x2
    {
        evercddl_COSE_Untagged_Message_ugly::Inl { v: x3 } =>
          evercddl_COSE_Untagged_Message::Mkevercddl_COSE_Untagged_Message0 { _x0: x3 },
        evercddl_COSE_Untagged_Message_ugly::Inr { v: x4 } =>
          evercddl_COSE_Untagged_Message::Mkevercddl_COSE_Untagged_Message1 { _x0: x4 },
        _ => panic!("Incomplete pattern matching")
    }
}

fn evercddl_COSE_Untagged_Message_left <'a>(x7: evercddl_COSE_Untagged_Message <'a>) ->
    evercddl_COSE_Untagged_Message_ugly
    <'a>
{
    match x7
    {
        evercddl_COSE_Untagged_Message::Mkevercddl_COSE_Untagged_Message0 { _x0: x10 } =>
          evercddl_COSE_Untagged_Message_ugly::Inl { v: x10 },
        evercddl_COSE_Untagged_Message::Mkevercddl_COSE_Untagged_Message1 { _x0: x12 } =>
          evercddl_COSE_Untagged_Message_ugly::Inr { v: x12 },
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Parser for evercddl_COSE_Untagged_Message
*/
pub fn
parse_COSE_Untagged_Message
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_COSE_Untagged_Message
    <'a>
{
    let test: bool = validate_COSE_Sign(c);
    let res1: evercddl_COSE_Untagged_Message_ugly =
        if test
        {
            let res: evercddl_COSE_Sign = parse_COSE_Sign(c);
            evercddl_COSE_Untagged_Message_ugly::Inl { v: res }
        }
        else
        {
            let res: evercddl_COSE_Sign1 = parse_COSE_Sign1(c);
            evercddl_COSE_Untagged_Message_ugly::Inr { v: res }
        };
    evercddl_COSE_Untagged_Message_right(res1)
}

/**
Serializer for evercddl_COSE_Untagged_Message
*/
pub fn
serialize_COSE_Untagged_Message(c: evercddl_COSE_Untagged_Message, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_COSE_Untagged_Message_ugly = evercddl_COSE_Untagged_Message_left(c);
    match c·
    {
        evercddl_COSE_Untagged_Message_ugly::Inl { v: c1 } => serialize_COSE_Sign(c1, out),
        evercddl_COSE_Untagged_Message_ugly::Inr { v: c2 } => serialize_COSE_Sign1(c2, out),
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_COSE_Untagged_Message···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_COSE_Untagged_Message <'a>, &'a [u8]) }
}

pub fn validate_and_parse_COSE_Untagged_Message <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_COSE_Untagged_Message···Pulse_Lib_Slice_slice·uint8_t·
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
          option__·COSE_Format_evercddl_COSE_Untagged_Message···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_COSE_Untagged_Message = parse_COSE_Untagged_Message(rl);
                  option__·COSE_Format_evercddl_COSE_Untagged_Message···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_COSE_Untagged_Message···Pulse_Lib_Slice_slice·uint8_t·::None
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
enum evercddl_COSE_Messages_ugly <'a>
{
    Inl { v: evercddl_COSE_Untagged_Message <'a> },
    Inr { v: evercddl_COSE_Tagged_Message <'a> }
}

#[derive(PartialEq, Clone, Copy)]
enum evercddl_COSE_Messages_tags
{
    Mkevercddl_COSE_Messages0,
    Mkevercddl_COSE_Messages1
}

#[derive(PartialEq, Clone, Copy)]
pub enum evercddl_COSE_Messages <'a>
{
    Mkevercddl_COSE_Messages0 { _x0: evercddl_COSE_Untagged_Message <'a> },
    Mkevercddl_COSE_Messages1 { _x0: evercddl_COSE_Tagged_Message <'a> }
}

pub fn uu___is_Mkevercddl_COSE_Messages0(projectee: evercddl_COSE_Messages) -> bool
{
    match projectee
    { evercddl_COSE_Messages::Mkevercddl_COSE_Messages0 { .. } => true, _ => false }
}

pub fn uu___is_Mkevercddl_COSE_Messages1(projectee: evercddl_COSE_Messages) -> bool
{
    match projectee
    { evercddl_COSE_Messages::Mkevercddl_COSE_Messages1 { .. } => true, _ => false }
}

fn evercddl_COSE_Messages_right <'a>(x2: evercddl_COSE_Messages_ugly <'a>) ->
    evercddl_COSE_Messages
    <'a>
{
    match x2
    {
        evercddl_COSE_Messages_ugly::Inl { v: x3 } =>
          evercddl_COSE_Messages::Mkevercddl_COSE_Messages0 { _x0: x3 },
        evercddl_COSE_Messages_ugly::Inr { v: x4 } =>
          evercddl_COSE_Messages::Mkevercddl_COSE_Messages1 { _x0: x4 },
        _ => panic!("Incomplete pattern matching")
    }
}

fn evercddl_COSE_Messages_left <'a>(x7: evercddl_COSE_Messages <'a>) ->
    evercddl_COSE_Messages_ugly
    <'a>
{
    match x7
    {
        evercddl_COSE_Messages::Mkevercddl_COSE_Messages0 { _x0: x10 } =>
          evercddl_COSE_Messages_ugly::Inl { v: x10 },
        evercddl_COSE_Messages::Mkevercddl_COSE_Messages1 { _x0: x12 } =>
          evercddl_COSE_Messages_ugly::Inr { v: x12 },
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Parser for evercddl_COSE_Messages
*/
pub fn
parse_COSE_Messages
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_COSE_Messages
    <'a>
{
    let test: bool = validate_COSE_Untagged_Message(c);
    let res1: evercddl_COSE_Messages_ugly =
        if test
        {
            let res: evercddl_COSE_Untagged_Message = parse_COSE_Untagged_Message(c);
            evercddl_COSE_Messages_ugly::Inl { v: res }
        }
        else
        {
            let res: evercddl_COSE_Tagged_Message = parse_COSE_Tagged_Message(c);
            evercddl_COSE_Messages_ugly::Inr { v: res }
        };
    evercddl_COSE_Messages_right(res1)
}

/**
Serializer for evercddl_COSE_Messages
*/
pub fn
serialize_COSE_Messages(c: evercddl_COSE_Messages, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_COSE_Messages_ugly = evercddl_COSE_Messages_left(c);
    match c·
    {
        evercddl_COSE_Messages_ugly::Inl { v: c1 } => serialize_COSE_Untagged_Message(c1, out),
        evercddl_COSE_Messages_ugly::Inr { v: c2 } => serialize_COSE_Tagged_Message(c2, out),
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_COSE_Messages···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_COSE_Messages <'a>, &'a [u8]) }
}

pub fn validate_and_parse_COSE_Messages <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_COSE_Messages···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_COSE_Messages···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_COSE_Messages = parse_COSE_Messages(rl);
                  option__·COSE_Format_evercddl_COSE_Messages···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_COSE_Messages···Pulse_Lib_Slice_slice·uint8_t·::None
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_Internal_Types(c: crate::cbordetveraux::cbor_raw) -> bool
{ validate_Sig_structure(c) }

pub type evercddl_Internal_Types <'a> = evercddl_Sig_structure <'a>;

pub fn uu___is_Mkevercddl_Internal_Types0(projectee: evercddl_Sig_structure) -> bool
{
    crate::lowstar::ignore::ignore::<evercddl_Sig_structure>(projectee);
    true
}

fn evercddl_Internal_Types_right <'a>(x1: evercddl_Sig_structure <'a>) ->
    evercddl_Sig_structure
    <'a>
{ x1 }

fn evercddl_Internal_Types_left <'a>(x3: evercddl_Sig_structure <'a>) ->
    evercddl_Sig_structure
    <'a>
{ x3 }

/**
Parser for evercddl_Internal_Types
*/
pub fn
parse_Internal_Types
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_Sig_structure
    <'a>
{
    let res1: evercddl_Sig_structure = parse_Sig_structure(c);
    evercddl_Internal_Types_right(res1)
}

/**
Serializer for evercddl_Internal_Types
*/
pub fn
serialize_Internal_Types(c: evercddl_Sig_structure, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_Sig_structure = evercddl_Internal_Types_left(c);
    serialize_Sig_structure(c·, out)
}

#[derive(PartialEq, Clone, Copy)]
pub enum
option__·COSE_Format_evercddl_Internal_Types···Pulse_Lib_Slice_slice·uint8_t·
<'a>
{
    None,
    Some { v: (evercddl_Sig_structure <'a>, &'a [u8]) }
}

pub fn validate_and_parse_Internal_Types <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_Internal_Types···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_Internal_Types···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_Sig_structure = parse_Internal_Types(rl);
                  option__·COSE_Format_evercddl_Internal_Types···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              {
                  option__·COSE_Format_evercddl_Internal_Types···Pulse_Lib_Slice_slice·uint8_t·::None
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
enum evercddl_start_ugly <'a>
{
    Inl { v: evercddl_COSE_Messages <'a> },
    Inr { v: evercddl_Sig_structure <'a> }
}

#[derive(PartialEq, Clone, Copy)]
enum evercddl_start_tags
{
    Mkevercddl_start0,
    Mkevercddl_start1
}

#[derive(PartialEq, Clone, Copy)]
pub enum evercddl_start <'a>
{
    Mkevercddl_start0 { _x0: evercddl_COSE_Messages <'a> },
    Mkevercddl_start1 { _x0: evercddl_Sig_structure <'a> }
}

pub fn uu___is_Mkevercddl_start0(projectee: evercddl_start) -> bool
{ match projectee { evercddl_start::Mkevercddl_start0 { .. } => true, _ => false } }

pub fn uu___is_Mkevercddl_start1(projectee: evercddl_start) -> bool
{ match projectee { evercddl_start::Mkevercddl_start1 { .. } => true, _ => false } }

fn evercddl_start_right <'a>(x2: evercddl_start_ugly <'a>) -> evercddl_start <'a>
{
    match x2
    {
        evercddl_start_ugly::Inl { v: x3 } => evercddl_start::Mkevercddl_start0 { _x0: x3 },
        evercddl_start_ugly::Inr { v: x4 } => evercddl_start::Mkevercddl_start1 { _x0: x4 },
        _ => panic!("Incomplete pattern matching")
    }
}

fn evercddl_start_left <'a>(x7: evercddl_start <'a>) -> evercddl_start_ugly <'a>
{
    match x7
    {
        evercddl_start::Mkevercddl_start0 { _x0: x10 } => evercddl_start_ugly::Inl { v: x10 },
        evercddl_start::Mkevercddl_start1 { _x0: x12 } => evercddl_start_ugly::Inr { v: x12 },
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Parser for evercddl_start
*/
pub fn
parse_start
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    evercddl_start
    <'a>
{
    let test: bool = validate_COSE_Messages(c);
    let res1: evercddl_start_ugly =
        if test
        {
            let res: evercddl_COSE_Messages = parse_COSE_Messages(c);
            evercddl_start_ugly::Inl { v: res }
        }
        else
        {
            let res: evercddl_Sig_structure = parse_Internal_Types(c);
            evercddl_start_ugly::Inr { v: res }
        };
    evercddl_start_right(res1)
}

/**
Serializer for evercddl_start
*/
pub fn
serialize_start(c: evercddl_start, out: &mut [u8]) ->
    usize
{
    let c·: evercddl_start_ugly = evercddl_start_left(c);
    match c·
    {
        evercddl_start_ugly::Inl { v: c1 } => serialize_COSE_Messages(c1, out),
        evercddl_start_ugly::Inr { v: c2 } => serialize_Internal_Types(c2, out),
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·COSE_Format_evercddl_start···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (evercddl_start <'a>, &'a [u8]) }
}

pub fn validate_and_parse_start <'a>(s: &'a [u8]) ->
    option__·COSE_Format_evercddl_start···Pulse_Lib_Slice_slice·uint8_t·
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
        => option__·COSE_Format_evercddl_start···Pulse_Lib_Slice_slice·uint8_t·::None,
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
                  let x: evercddl_start = parse_start(rl);
                  option__·COSE_Format_evercddl_start···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·COSE_Format_evercddl_start···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}
