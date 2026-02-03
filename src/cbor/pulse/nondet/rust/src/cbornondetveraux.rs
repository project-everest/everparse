#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

const _zero_for_deref: u32 = 0u32;

#[derive(PartialEq, Clone, Copy)] pub struct raw_uint64 { pub size: u8, pub value: u64 }

fn get_bitfield_gen8(x: u8, lo: u32, hi: u32) -> u8
{
    let op1: u8 = x.wrapping_shl(8u32.wrapping_sub(hi));
    op1.wrapping_shr(8u32.wrapping_sub(hi).wrapping_add(lo))
}

fn set_bitfield_gen8(x: u8, lo: u32, hi: u32, v: u8) -> u8
{
    let op0: u8 = 255u8;
    let op1: u8 = op0.wrapping_shr(8u32.wrapping_sub(hi.wrapping_sub(lo)));
    let op2: u8 = op1.wrapping_shl(lo);
    let op3: u8 = ! op2;
    let op4: u8 = x & op3;
    let op5: u8 = v.wrapping_shl(lo);
    op4 | op5
}

const additional_info_long_argument_8_bits: u8 = 24u8;

const additional_info_unassigned_min: u8 = 28u8;

#[derive(PartialEq, Clone, Copy)]
struct initial_byte_t
{ pub major_type: u8, pub additional_info: u8 }

const additional_info_long_argument_16_bits: u8 = 25u8;

const additional_info_long_argument_32_bits: u8 = 26u8;

const additional_info_long_argument_64_bits: u8 = 27u8;

#[derive(PartialEq, Clone, Copy)]
enum long_argument_tags
{
    LongArgumentSimpleValue,
    LongArgumentU8,
    LongArgumentU16,
    LongArgumentU32,
    LongArgumentU64,
    LongArgumentOther
}

#[derive(PartialEq, Clone, Copy)]
enum long_argument
{
    LongArgumentSimpleValue { v: u8 },
    LongArgumentU8 { v: u8 },
    LongArgumentU16 { v: u16 },
    LongArgumentU32 { v: u32 },
    LongArgumentU64 { v: u64 },
    LongArgumentOther
}

#[derive(PartialEq, Clone, Copy)]
struct header
{ pub fst: initial_byte_t, pub snd: long_argument }

fn argument_as_uint64(b: initial_byte_t, x: long_argument) -> u64
{
    match x
    {
        long_argument::LongArgumentU8 { v } => raw_uint64 { size: 1u8, value: v as u64 },
        long_argument::LongArgumentU16 { v } => raw_uint64 { size: 2u8, value: v as u64 },
        long_argument::LongArgumentU32 { v } => raw_uint64 { size: 3u8, value: v as u64 },
        long_argument::LongArgumentU64 { v } => raw_uint64 { size: 4u8, value: v },
        long_argument::LongArgumentOther =>
          raw_uint64 { size: 0u8, value: b.additional_info as u64 },
        _ => panic!("Incomplete pattern matching")
    }.value
}

fn raw_uint64_as_argument(t: u8, x: raw_uint64) -> header
{
    if x.size == 0u8
    {
        header
        {
            fst: initial_byte_t { major_type: t, additional_info: x.value as u8 },
            snd: long_argument::LongArgumentOther
        }
    }
    else if x.size == 1u8
    {
        header
        {
            fst:
            initial_byte_t { major_type: t, additional_info: additional_info_long_argument_8_bits },
            snd: long_argument::LongArgumentU8 { v: x.value as u8 }
        }
    }
    else if x.size == 2u8
    {
        header
        {
            fst:
            initial_byte_t { major_type: t, additional_info: additional_info_long_argument_16_bits },
            snd: long_argument::LongArgumentU16 { v: x.value as u16 }
        }
    }
    else if x.size == 3u8
    {
        header
        {
            fst:
            initial_byte_t { major_type: t, additional_info: additional_info_long_argument_32_bits },
            snd: long_argument::LongArgumentU32 { v: x.value as u32 }
        }
    }
    else
    {
        header
        {
            fst:
            initial_byte_t { major_type: t, additional_info: additional_info_long_argument_64_bits },
            snd: long_argument::LongArgumentU64 { v: x.value }
        }
    }
}

fn simple_value_as_argument(x: u8) -> header
{
    if x <= max_simple_value_additional_info
    {
        header
        {
            fst: initial_byte_t { major_type: cbor_major_type_simple_value, additional_info: x },
            snd: long_argument::LongArgumentOther
        }
    }
    else
    {
        header
        {
            fst:
            initial_byte_t
            {
                major_type: cbor_major_type_simple_value,
                additional_info: additional_info_long_argument_8_bits
            },
            snd: long_argument::LongArgumentSimpleValue { v: x }
        }
    }
}

fn get_header_major_type(h: header) -> u8
{
    let b: initial_byte_t = h.fst;
    b.major_type
}

pub(crate) fn impl_correct(s: &[u8]) -> bool
{
    let mut pres: [bool; 1] = [true; 1usize];
    let mut pi: [usize; 1] = [0usize; 1usize];
    let len: usize = s.len();
    let res: bool = (&pres)[0];
    let mut cond: bool =
        if res
        {
            let i: usize = (&pi)[0];
            i < len
        }
        else
        { false };
    while
    cond
    {
        let i: usize = (&pi)[0];
        let byte1: u8 = s[i];
        let i1: usize = i.wrapping_add(1usize);
        if byte1 <= 0x7Fu8
        { (&mut pi)[0] = i1 }
        else if i1 == len
        { (&mut pres)[0] = false }
        else
        {
            let byte2: u8 = s[i1];
            let i2: usize = i1.wrapping_add(1usize);
            if 0xC2u8 <= byte1 && byte1 <= 0xDFu8 && (0x80u8 <= byte2 && byte2 <= 0xBFu8)
            { (&mut pi)[0] = i2 }
            else if i2 == len
            { (&mut pres)[0] = false }
            else
            {
                let byte3: u8 = s[i2];
                let i3: usize = i2.wrapping_add(1usize);
                if ! (0x80u8 <= byte3 && byte3 <= 0xBFu8)
                { (&mut pres)[0] = false }
                else if byte1 == 0xE0u8
                {
                    if 0xA0u8 <= byte2 && byte2 <= 0xBFu8
                    { (&mut pi)[0] = i3 }
                    else
                    { (&mut pres)[0] = false }
                }
                else if byte1 == 0xEDu8
                {
                    if 0x80u8 <= byte2 && byte2 <= 0x9Fu8
                    { (&mut pi)[0] = i3 }
                    else
                    { (&mut pres)[0] = false }
                }
                else if 0xE1u8 <= byte1 && byte1 <= 0xEFu8 && (0x80u8 <= byte2 && byte2 <= 0xBFu8)
                { (&mut pi)[0] = i3 }
                else if i3 == len
                { (&mut pres)[0] = false }
                else
                {
                    let byte4: u8 = s[i3];
                    let i4: usize = i3.wrapping_add(1usize);
                    if ! (0x80u8 <= byte4 && byte4 <= 0xBFu8)
                    { (&mut pres)[0] = false }
                    else if byte1 == 0xF0u8 && 0x90u8 <= byte2 && byte2 <= 0xBFu8
                    { (&mut pi)[0] = i4 }
                    else if
                    0xF1u8 <= byte1 && byte1 <= 0xF3u8 && (0x80u8 <= byte2 && byte2 <= 0xBFu8)
                    { (&mut pi)[0] = i4 }
                    else if byte1 == 0xF4u8 && 0x80u8 <= byte2 && byte2 <= 0x8Fu8
                    { (&mut pi)[0] = i4 }
                    else
                    { (&mut pres)[0] = false }
                }
            }
        };
        let res0: bool = (&pres)[0];
        let ite: bool =
            if res0
            {
                let i0: usize = (&pi)[0];
                i0 < len
            }
            else
            { false };
        cond = ite
    };
    (&pres)[0]
}

#[derive(PartialEq, Clone, Copy)]
enum option__bool_tags
{
    None,
    Some
}

#[derive(PartialEq, Clone, Copy)]
pub(crate) enum option__bool
{
    None,
    Some { v: bool }
}

fn eq_Some_true(x: option__bool) -> bool
{ match x { option__bool::Some { v: b } => b, _ => false } }

fn eq_Some_false(x: option__bool) -> bool
{ match x { option__bool::Some { v: b } => ! b, _ => false } }

#[derive(PartialEq, Clone, Copy)]
pub enum option__size_t
{
    None,
    Some { v: usize }
}

fn eq_Some_0sz(x: option__size_t) -> bool
{ match x { option__size_t::Some { v: y } => y == 0usize, _ => false } }

#[derive(PartialEq, Clone, Copy)]
pub struct cbor_raw_serialized_iterator <'a>
{ pub s: &'a [u8], pub len: u64 }

fn mk_raw_uint64(x: u64) -> raw_uint64
{
    let size: u8 =
        if x <= max_simple_value_additional_info as u64
        { 0u8 }
        else if x < 256u64
        { 1u8 }
        else if x < 65536u64 { 2u8 } else if x < 4294967296u64 { 3u8 } else { 4u8 };
    raw_uint64 { size, value: x }
}

#[derive(PartialEq, Clone, Copy)]
pub struct cbor_string <'a>
{ pub cbor_string_type: u8, pub cbor_string_size: u8, pub cbor_string_ptr: &'a [u8] }

fn cbor_string_reset_perm <'a>(c: cbor_string <'a>) -> cbor_string <'a>
{
    cbor_string
    {
        cbor_string_type: c.cbor_string_type,
        cbor_string_size: c.cbor_string_size,
        cbor_string_ptr: c.cbor_string_ptr
    }
}

#[derive(PartialEq, Clone, Copy)]
pub struct cbor_serialized <'a>
{ pub cbor_serialized_header: raw_uint64, pub cbor_serialized_payload: &'a [u8] }

fn cbor_serialized_reset_perm <'a>(c: cbor_serialized <'a>) -> cbor_serialized <'a>
{
    cbor_serialized
    {
        cbor_serialized_header: c.cbor_serialized_header,
        cbor_serialized_payload: c.cbor_serialized_payload
    }
}

#[derive(PartialEq, Clone, Copy)]
pub struct cbor_tagged <'a>
{ pub cbor_tagged_tag: raw_uint64, pub cbor_tagged_ptr: &'a [cbor_raw <'a>] }

fn cbor_tagged_reset_perm <'a>(c: cbor_tagged <'a>) -> cbor_tagged <'a>
{ cbor_tagged { cbor_tagged_tag: c.cbor_tagged_tag, cbor_tagged_ptr: c.cbor_tagged_ptr } }

#[derive(PartialEq, Clone, Copy)]
pub struct cbor_int
{ pub cbor_int_type: u8, pub cbor_int_size: u8, pub cbor_int_value: u64 }

#[derive(PartialEq, Clone, Copy)]
pub struct cbor_map_entry <'a>
{ pub cbor_map_entry_key: cbor_raw <'a>, pub cbor_map_entry_value: cbor_raw <'a> }

#[derive(PartialEq, Clone, Copy)]
pub struct cbor_map <'a>
{ pub cbor_map_length_size: u8, pub cbor_map_ptr: &'a [cbor_map_entry <'a>] }

#[derive(PartialEq, Clone, Copy)]
enum cbor_raw_tags
{
    CBOR_Case_Int,
    CBOR_Case_Simple,
    CBOR_Case_String,
    CBOR_Case_Tagged,
    CBOR_Case_Array,
    CBOR_Case_Map,
    CBOR_Case_Serialized_Tagged,
    CBOR_Case_Serialized_Array,
    CBOR_Case_Serialized_Map
}

#[derive(PartialEq, Clone, Copy)]
pub enum cbor_raw <'a>
{
    CBOR_Case_Int { v: cbor_int },
    CBOR_Case_Simple { v: u8 },
    CBOR_Case_String { v: cbor_string <'a> },
    CBOR_Case_Tagged { v: cbor_tagged <'a> },
    CBOR_Case_Array { v: cbor_array <'a> },
    CBOR_Case_Map { v: cbor_map <'a> },
    CBOR_Case_Serialized_Tagged { v: cbor_serialized <'a> },
    CBOR_Case_Serialized_Array { v: cbor_serialized <'a> },
    CBOR_Case_Serialized_Map { v: cbor_serialized <'a> }
}

#[derive(PartialEq, Clone, Copy)]
pub struct cbor_array <'a>
{ pub cbor_array_length_size: u8, pub cbor_array_ptr: &'a [cbor_raw <'a>] }

fn cbor_array_reset_perm <'a>(c: cbor_array <'a>) -> cbor_array <'a>
{
    cbor_array
    { cbor_array_length_size: c.cbor_array_length_size, cbor_array_ptr: c.cbor_array_ptr }
}

fn cbor_map_reset_perm <'a>(c: cbor_map <'a>) -> cbor_map <'a>
{ cbor_map { cbor_map_length_size: c.cbor_map_length_size, cbor_map_ptr: c.cbor_map_ptr } }

pub(crate) fn cbor_raw_reset_perm_tot <'a>(c: cbor_raw <'a>) -> cbor_raw <'a>
{
    match c
    {
        cbor_raw::CBOR_Case_String { v } =>
          cbor_raw::CBOR_Case_String { v: cbor_string_reset_perm(v) },
        cbor_raw::CBOR_Case_Tagged { v } =>
          cbor_raw::CBOR_Case_Tagged { v: cbor_tagged_reset_perm(v) },
        cbor_raw::CBOR_Case_Array { v } => cbor_raw::CBOR_Case_Array { v: cbor_array_reset_perm(v) },
        cbor_raw::CBOR_Case_Map { v } => cbor_raw::CBOR_Case_Map { v: cbor_map_reset_perm(v) },
        cbor_raw::CBOR_Case_Serialized_Tagged { v } =>
          cbor_raw::CBOR_Case_Serialized_Tagged { v: cbor_serialized_reset_perm(v) },
        cbor_raw::CBOR_Case_Serialized_Array { v } =>
          cbor_raw::CBOR_Case_Serialized_Array { v: cbor_serialized_reset_perm(v) },
        cbor_raw::CBOR_Case_Serialized_Map { v } =>
          cbor_raw::CBOR_Case_Serialized_Map { v: cbor_serialized_reset_perm(v) },
        _ => c
    }
}

fn impl_uint8_compare(x1: u8, x2: u8) -> i16
{ if x1 < x2 { -1i16 } else if x1 > x2 { 1i16 } else { 0i16 } }

fn lex_compare_bytes(s1: &[u8], s2: &[u8]) -> i16
{
    let sp1: &[u8] = s1;
    let sp2: &[u8] = s2;
    let mut pi1: [usize; 1] = [0usize; 1usize];
    let mut pi2: [usize; 1] = [0usize; 1usize];
    let n1: usize = sp1.len();
    let n2: usize = sp2.len();
    let ite: i16 =
        if 0usize < n1
        { if 0usize < n2 { 0i16 } else { 1i16 } }
        else if 0usize < n2 { -1i16 } else { 0i16 };
    let mut pres: [i16; 1] = [ite; 1usize];
    let res: i16 = (&pres)[0];
    let i1: usize = (&pi1)[0];
    let mut cond: bool = res == 0i16 && i1 < n1;
    while
    cond
    {
        let i10: usize = (&pi1)[0];
        let x1: u8 = sp1[i10];
        let i2: usize = (&pi2)[0];
        let x2: u8 = sp2[i2];
        let c: i16 = impl_uint8_compare(x1, x2);
        if c == 0i16
        {
            let i1·: usize = i10.wrapping_add(1usize);
            let i2·: usize = i2.wrapping_add(1usize);
            let ci1·: bool = i1· < n1;
            let ci2·: bool = i2· < n2;
            if ci2· && ! ci1·
            { (&mut pres)[0] = -1i16 }
            else if ci1· && ! ci2·
            { (&mut pres)[0] = 1i16 }
            else
            {
                (&mut pi1)[0] = i1·;
                (&mut pi2)[0] = i2·
            }
        }
        else
        { (&mut pres)[0] = c };
        let res0: i16 = (&pres)[0];
        let i11: usize = (&pi1)[0];
        cond = res0 == 0i16 && i11 < n1
    };
    (&pres)[0]
}

fn read_initial_byte_t(input: &[u8]) -> initial_byte_t
{
    let last: u8 = input[0usize];
    let x: u8 = last;
    initial_byte_t
    {
        major_type: get_bitfield_gen8(x, 5u32, 8u32),
        additional_info: get_bitfield_gen8(x, 0u32, 5u32)
    }
}

fn read_header(input: &[u8]) -> header
{
    let i: usize = 1usize;
    let s: (&[u8], &[u8]) = input.split_at(i);
    let _letpattern: (&[u8], &[u8]) =
        {
            let s1: &[u8] = s.0;
            let s2: &[u8] = s.1;
            (s1,s2)
        };
    let _letpattern0: (&[u8], &[u8]) =
        {
            let input1: &[u8] = _letpattern.0;
            let input2: &[u8] = _letpattern.1;
            (input1,input2)
        };
    let input1: &[u8] = _letpattern0.0;
    let input2: &[u8] = _letpattern0.1;
    let x: initial_byte_t = read_initial_byte_t(input1);
    let x1: initial_byte_t = x;
    let x2: long_argument =
        if x1.additional_info == additional_info_long_argument_8_bits
        {
            if x1.major_type == cbor_major_type_simple_value
            {
                let last: u8 = input2[0usize];
                let x0: u8 = last;
                long_argument::LongArgumentSimpleValue { v: x0 }
            }
            else
            {
                let last: u8 = input2[0usize];
                let x0: u8 = last;
                long_argument::LongArgumentU8 { v: x0 }
            }
        }
        else if x1.additional_info == additional_info_long_argument_16_bits
        {
            let pos·: usize = 1usize;
            let last: u8 = input2[pos·];
            let last1: u8 = input2[0usize];
            let n: u16 = last1 as u16;
            let blast: u16 = last as u16;
            let x0: u16 = blast.wrapping_add(n.wrapping_mul(256u16));
            long_argument::LongArgumentU16 { v: x0 }
        }
        else if x1.additional_info == additional_info_long_argument_32_bits
        {
            let pos·: usize = 3usize;
            let last: u8 = input2[pos·];
            let pos·1: usize = pos·.wrapping_sub(1usize);
            let last1: u8 = input2[pos·1];
            let pos·2: usize = pos·1.wrapping_sub(1usize);
            let last2: u8 = input2[pos·2];
            let last3: u8 = input2[0usize];
            let n: u32 = last3 as u32;
            let blast: u32 = last2 as u32;
            let n0: u32 = blast.wrapping_add(n.wrapping_mul(256u32));
            let blast0: u32 = last1 as u32;
            let n1: u32 = blast0.wrapping_add(n0.wrapping_mul(256u32));
            let blast1: u32 = last as u32;
            let x0: u32 = blast1.wrapping_add(n1.wrapping_mul(256u32));
            long_argument::LongArgumentU32 { v: x0 }
        }
        else if x1.additional_info == additional_info_long_argument_64_bits
        {
            let pos·: usize = 7usize;
            let last: u8 = input2[pos·];
            let pos·1: usize = pos·.wrapping_sub(1usize);
            let last1: u8 = input2[pos·1];
            let pos·2: usize = pos·1.wrapping_sub(1usize);
            let last2: u8 = input2[pos·2];
            let pos·3: usize = pos·2.wrapping_sub(1usize);
            let last3: u8 = input2[pos·3];
            let pos·4: usize = pos·3.wrapping_sub(1usize);
            let last4: u8 = input2[pos·4];
            let pos·5: usize = pos·4.wrapping_sub(1usize);
            let last5: u8 = input2[pos·5];
            let pos·6: usize = pos·5.wrapping_sub(1usize);
            let last6: u8 = input2[pos·6];
            let last7: u8 = input2[0usize];
            let n: u64 = last7 as u64;
            let blast: u64 = last6 as u64;
            let n0: u64 = blast.wrapping_add(n.wrapping_mul(256u64));
            let blast0: u64 = last5 as u64;
            let n1: u64 = blast0.wrapping_add(n0.wrapping_mul(256u64));
            let blast1: u64 = last4 as u64;
            let n2: u64 = blast1.wrapping_add(n1.wrapping_mul(256u64));
            let blast2: u64 = last3 as u64;
            let n3: u64 = blast2.wrapping_add(n2.wrapping_mul(256u64));
            let blast3: u64 = last2 as u64;
            let n4: u64 = blast3.wrapping_add(n3.wrapping_mul(256u64));
            let blast4: u64 = last1 as u64;
            let n5: u64 = blast4.wrapping_add(n4.wrapping_mul(256u64));
            let blast5: u64 = last as u64;
            let x0: u64 = blast5.wrapping_add(n5.wrapping_mul(256u64));
            long_argument::LongArgumentU64 { v: x0 }
        }
        else
        { long_argument::LongArgumentOther };
    header { fst: x1, snd: x2 }
}

fn validate_header(input: &[u8], poffset: &mut [usize]) -> bool
{
    let offset1: usize = poffset[0];
    let offset2: usize = poffset[0];
    let offset3: usize = poffset[0];
    let is_valid: bool =
        if input.len().wrapping_sub(offset3) < 1usize
        { false }
        else
        {
            poffset[0] = offset3.wrapping_add(1usize);
            true
        };
    let is_valid1: bool =
        if is_valid
        {
            let off: usize = poffset[0];
            let s·: (&[u8], &[u8]) = input.split_at(offset2);
            let _letpattern: (&[u8], &[u8]) =
                {
                    let s1: &[u8] = s·.0;
                    let s2: &[u8] = s·.1;
                    (s1,s2)
                };
            let input·: &[u8] =
                {
                    let _input1: &[u8] = _letpattern.0;
                    let input23: &[u8] = _letpattern.1;
                    let consumed: usize = off.wrapping_sub(offset2);
                    let _letpattern1: (&[u8], &[u8]) = input23.split_at(consumed);
                    let _letpattern10: (&[u8], &[u8]) =
                        {
                            let s1: &[u8] = _letpattern1.0;
                            let s2: &[u8] = _letpattern1.1;
                            (s1,s2)
                        };
                    let _letpattern11: (&[u8], &[u8]) =
                        {
                            let left: &[u8] = _letpattern10.0;
                            let right: &[u8] = _letpattern10.1;
                            (left,right)
                        };
                    let input2: &[u8] = _letpattern11.0;
                    let _input3: &[u8] = _letpattern11.1;
                    input2
                };
            let x: initial_byte_t = read_initial_byte_t(input·);
            let ite: bool =
                if x.major_type == cbor_major_type_simple_value
                { x.additional_info <= additional_info_long_argument_8_bits }
                else
                { true };
            ite && x.additional_info < additional_info_unassigned_min
        }
        else
        { false };
    if is_valid1
    {
        let off: usize = poffset[0];
        let s·: (&[u8], &[u8]) = input.split_at(offset1);
        let _letpattern: (&[u8], &[u8]) =
            {
                let s1: &[u8] = s·.0;
                let s2: &[u8] = s·.1;
                (s1,s2)
            };
        let input·: &[u8] =
            {
                let _input1: &[u8] = _letpattern.0;
                let input23: &[u8] = _letpattern.1;
                let consumed: usize = off.wrapping_sub(offset1);
                let _letpattern1: (&[u8], &[u8]) = input23.split_at(consumed);
                let _letpattern10: (&[u8], &[u8]) =
                    {
                        let s1: &[u8] = _letpattern1.0;
                        let s2: &[u8] = _letpattern1.1;
                        (s1,s2)
                    };
                let _letpattern11: (&[u8], &[u8]) =
                    {
                        let left: &[u8] = _letpattern10.0;
                        let right: &[u8] = _letpattern10.1;
                        (left,right)
                    };
                let input2: &[u8] = _letpattern11.0;
                let _input3: &[u8] = _letpattern11.1;
                input2
            };
        let x: initial_byte_t = read_initial_byte_t(input·);
        let x0: initial_byte_t = x;
        if x0.additional_info == additional_info_long_argument_8_bits
        {
            if x0.major_type == cbor_major_type_simple_value
            {
                let offset20: usize = poffset[0];
                let offset30: usize = poffset[0];
                let is_valid0: bool =
                    if input.len().wrapping_sub(offset30) < 1usize
                    { false }
                    else
                    {
                        poffset[0] = offset30.wrapping_add(1usize);
                        true
                    };
                if is_valid0
                {
                    let off1: usize = poffset[0];
                    let s·0: (&[u8], &[u8]) = input.split_at(offset20);
                    let _letpattern0: (&[u8], &[u8]) =
                        {
                            let s1: &[u8] = s·0.0;
                            let s2: &[u8] = s·0.1;
                            (s1,s2)
                        };
                    let input·0: &[u8] =
                        {
                            let _input1: &[u8] = _letpattern0.0;
                            let input23: &[u8] = _letpattern0.1;
                            let consumed: usize = off1.wrapping_sub(offset20);
                            let _letpattern1: (&[u8], &[u8]) = input23.split_at(consumed);
                            let _letpattern10: (&[u8], &[u8]) =
                                {
                                    let s1: &[u8] = _letpattern1.0;
                                    let s2: &[u8] = _letpattern1.1;
                                    (s1,s2)
                                };
                            let _letpattern11: (&[u8], &[u8]) =
                                {
                                    let left: &[u8] = _letpattern10.0;
                                    let right: &[u8] = _letpattern10.1;
                                    (left,right)
                                };
                            let input2: &[u8] = _letpattern11.0;
                            let _input3: &[u8] = _letpattern11.1;
                            input2
                        };
                    let last: u8 = input·0[0usize];
                    let x1: u8 = last;
                    min_simple_value_long_argument <= x1
                }
                else
                { false }
            }
            else
            {
                let offset20: usize = poffset[0];
                if input.len().wrapping_sub(offset20) < 1usize
                { false }
                else
                {
                    poffset[0] = offset20.wrapping_add(1usize);
                    true
                }
            }
        }
        else if x0.additional_info == additional_info_long_argument_16_bits
        {
            let offset20: usize = poffset[0];
            if input.len().wrapping_sub(offset20) < 2usize
            { false }
            else
            {
                poffset[0] = offset20.wrapping_add(2usize);
                true
            }
        }
        else if x0.additional_info == additional_info_long_argument_32_bits
        {
            let offset20: usize = poffset[0];
            if input.len().wrapping_sub(offset20) < 4usize
            { false }
            else
            {
                poffset[0] = offset20.wrapping_add(4usize);
                true
            }
        }
        else if x0.additional_info == additional_info_long_argument_64_bits
        {
            let offset20: usize = poffset[0];
            if input.len().wrapping_sub(offset20) < 8usize
            { false }
            else
            {
                poffset[0] = offset20.wrapping_add(8usize);
                true
            }
        }
        else
        { true }
    }
    else
    { false }
}

fn jump_header(input: &[u8], offset: usize) -> usize
{
    let off1: usize = offset.wrapping_add(1usize);
    let s·: (&[u8], &[u8]) = input.split_at(offset);
    let _letpattern: (&[u8], &[u8]) =
        {
            let s1: &[u8] = s·.0;
            let s2: &[u8] = s·.1;
            (s1,s2)
        };
    let input·: &[u8] =
        {
            let _input1: &[u8] = _letpattern.0;
            let input23: &[u8] = _letpattern.1;
            let consumed: usize = off1.wrapping_sub(offset);
            let _letpattern1: (&[u8], &[u8]) = input23.split_at(consumed);
            let _letpattern10: (&[u8], &[u8]) =
                {
                    let s1: &[u8] = _letpattern1.0;
                    let s2: &[u8] = _letpattern1.1;
                    (s1,s2)
                };
            let _letpattern11: (&[u8], &[u8]) =
                {
                    let left: &[u8] = _letpattern10.0;
                    let right: &[u8] = _letpattern10.1;
                    (left,right)
                };
            let input2: &[u8] = _letpattern11.0;
            let _input3: &[u8] = _letpattern11.1;
            input2
        };
    let x: initial_byte_t = read_initial_byte_t(input·);
    let x0: initial_byte_t = x;
    if x0.additional_info == additional_info_long_argument_8_bits
    { off1.wrapping_add(1usize) }
    else if x0.additional_info == additional_info_long_argument_16_bits
    { off1.wrapping_add(2usize) }
    else if x0.additional_info == additional_info_long_argument_32_bits
    { off1.wrapping_add(4usize) }
    else if x0.additional_info == additional_info_long_argument_64_bits
    { off1.wrapping_add(8usize) }
    else
    { off1.wrapping_add(0usize) }
}

fn validate_recursive_step_count_leaf(a: &[u8], bound: usize, prem: &mut [usize]) -> bool
{
    let i: usize = jump_header(a, 0usize);
    let s: (&[u8], &[u8]) = a.split_at(i);
    let _letpattern: (&[u8], &[u8]) =
        {
            let s1: &[u8] = s.0;
            let s2: &[u8] = s.1;
            (s1,s2)
        };
    let _letpattern0: (&[u8], &[u8]) =
        {
            let input1: &[u8] = _letpattern.0;
            let input2: &[u8] = _letpattern.1;
            (input1,input2)
        };
    let input1: &[u8] = _letpattern0.0;
    let _input2: &[u8] = _letpattern0.1;
    let h: header = read_header(input1);
    let typ: u8 = get_header_major_type(h);
    if typ == cbor_major_type_array
    {
        let b: initial_byte_t = h.fst;
        let l: long_argument = h.snd;
        let arg64: u64 = argument_as_uint64(b, l);
        prem[0] = arg64 as usize;
        false
    }
    else if typ == cbor_major_type_map
    {
        let b: initial_byte_t = h.fst;
        let l: long_argument = h.snd;
        let arg64: u64 = argument_as_uint64(b, l);
        let arg: usize = arg64 as usize;
        if arg > bound
        { true }
        else if bound.wrapping_sub(arg) < arg
        { true }
        else
        {
            prem[0] = arg.wrapping_add(arg);
            false
        }
    }
    else if typ == cbor_major_type_tagged
    {
        prem[0] = 1usize;
        false
    }
    else
    {
        prem[0] = 0usize;
        false
    }
}

fn impl_remaining_data_items_header(h: header) -> usize
{
    let typ: u8 = get_header_major_type(h);
    if typ == cbor_major_type_array
    {
        let b: initial_byte_t = h.fst;
        let l: long_argument = h.snd;
        let arg64: u64 = argument_as_uint64(b, l);
        arg64 as usize
    }
    else if typ == cbor_major_type_map
    {
        let b: initial_byte_t = h.fst;
        let l: long_argument = h.snd;
        let arg64: u64 = argument_as_uint64(b, l);
        let arg: usize = arg64 as usize;
        arg.wrapping_add(arg)
    }
    else if typ == cbor_major_type_tagged { 1usize } else { 0usize }
}

fn jump_recursive_step_count_leaf(a: &[u8]) -> usize
{
    let i: usize = jump_header(a, 0usize);
    let s: (&[u8], &[u8]) = a.split_at(i);
    let _letpattern: (&[u8], &[u8]) =
        {
            let s1: &[u8] = s.0;
            let s2: &[u8] = s.1;
            (s1,s2)
        };
    let _letpattern0: (&[u8], &[u8]) =
        {
            let input1: &[u8] = _letpattern.0;
            let input2: &[u8] = _letpattern.1;
            (input1,input2)
        };
    let input1: &[u8] = _letpattern0.0;
    let _input2: &[u8] = _letpattern0.1;
    let h: header = read_header(input1);
    impl_remaining_data_items_header(h)
}

fn validate_raw_data_item(input: &[u8], poffset: &mut [usize]) -> bool
{
    let mut pn: [usize; 1] = [1usize; 1usize];
    let mut pres: [bool; 1] = [true; 1usize];
    let res: bool = (&pres)[0];
    let n: usize = (&pn)[0];
    let mut cond: bool = res && n > 0usize;
    while
    cond
    {
        let off: usize = poffset[0];
        let n0: usize = (&pn)[0];
        if n0 > input.len().wrapping_sub(off)
        { (&mut pres)[0] = false }
        else
        {
            let offset1: usize = poffset[0];
            let is_valid1: bool = validate_header(input, poffset);
            let res1: bool =
                if is_valid1
                {
                    let off1: usize = poffset[0];
                    let s·: (&[u8], &[u8]) = input.split_at(offset1);
                    let _letpattern: (&[u8], &[u8]) =
                        {
                            let s1: &[u8] = s·.0;
                            let s2: &[u8] = s·.1;
                            (s1,s2)
                        };
                    let input·: &[u8] =
                        {
                            let _input1: &[u8] = _letpattern.0;
                            let input23: &[u8] = _letpattern.1;
                            let consumed: usize = off1.wrapping_sub(offset1);
                            let _letpattern1: (&[u8], &[u8]) = input23.split_at(consumed);
                            let _letpattern10: (&[u8], &[u8]) =
                                {
                                    let s1: &[u8] = _letpattern1.0;
                                    let s2: &[u8] = _letpattern1.1;
                                    (s1,s2)
                                };
                            let _letpattern11: (&[u8], &[u8]) =
                                {
                                    let left: &[u8] = _letpattern10.0;
                                    let right: &[u8] = _letpattern10.1;
                                    (left,right)
                                };
                            let input2: &[u8] = _letpattern11.0;
                            let _input3: &[u8] = _letpattern11.1;
                            input2
                        };
                    let x: header = read_header(input·);
                    let b: initial_byte_t = x.fst;
                    if
                    b.major_type == cbor_major_type_byte_string
                    ||
                    b.major_type == cbor_major_type_text_string
                    {
                        let b0: initial_byte_t = x.fst;
                        let l: long_argument = x.snd;
                        let n1: usize = argument_as_uint64(b0, l) as usize;
                        let offset2: usize = poffset[0];
                        let offset3: usize = poffset[0];
                        let is_valid: bool =
                            if input.len().wrapping_sub(offset3) < n1
                            { false }
                            else
                            {
                                poffset[0] = offset3.wrapping_add(n1);
                                true
                            };
                        if is_valid
                        {
                            let off2: usize = poffset[0];
                            let s·0: (&[u8], &[u8]) = input.split_at(offset2);
                            let _letpattern0: (&[u8], &[u8]) =
                                {
                                    let s1: &[u8] = s·0.0;
                                    let s2: &[u8] = s·0.1;
                                    (s1,s2)
                                };
                            let x1: &[u8] =
                                {
                                    let _input1: &[u8] = _letpattern0.0;
                                    let input23: &[u8] = _letpattern0.1;
                                    let consumed: usize = off2.wrapping_sub(offset2);
                                    let _letpattern1: (&[u8], &[u8]) = input23.split_at(consumed);
                                    let _letpattern10: (&[u8], &[u8]) =
                                        {
                                            let s1: &[u8] = _letpattern1.0;
                                            let s2: &[u8] = _letpattern1.1;
                                            (s1,s2)
                                        };
                                    let _letpattern11: (&[u8], &[u8]) =
                                        {
                                            let left: &[u8] = _letpattern10.0;
                                            let right: &[u8] = _letpattern10.1;
                                            (left,right)
                                        };
                                    let input2: &[u8] = _letpattern11.0;
                                    let _input3: &[u8] = _letpattern11.1;
                                    input2
                                };
                            if get_header_major_type(x) == cbor_major_type_byte_string
                            { true }
                            else
                            { impl_correct(x1) }
                        }
                        else
                        { false }
                    }
                    else
                    { true }
                }
                else
                { false };
            if ! res1
            { (&mut pres)[0] = false }
            else
            {
                let offset10: usize = poffset[0];
                let s·: (&[u8], &[u8]) = input.split_at(off);
                let _letpattern: (&[u8], &[u8]) =
                    {
                        let s1: &[u8] = s·.0;
                        let s2: &[u8] = s·.1;
                        (s1,s2)
                    };
                let input1: &[u8] =
                    {
                        let _input1: &[u8] = _letpattern.0;
                        let input23: &[u8] = _letpattern.1;
                        let consumed: usize = offset10.wrapping_sub(off);
                        let _letpattern1: (&[u8], &[u8]) = input23.split_at(consumed);
                        let _letpattern10: (&[u8], &[u8]) =
                            {
                                let s1: &[u8] = _letpattern1.0;
                                let s2: &[u8] = _letpattern1.1;
                                (s1,s2)
                            };
                        let _letpattern11: (&[u8], &[u8]) =
                            {
                                let left: &[u8] = _letpattern10.0;
                                let right: &[u8] = _letpattern10.1;
                                (left,right)
                            };
                        let input2: &[u8] = _letpattern11.0;
                        let _input3: &[u8] = _letpattern11.1;
                        input2
                    };
                let bound: usize = input.len().wrapping_sub(off).wrapping_sub(n0);
                let res2: bool = validate_recursive_step_count_leaf(input1, bound, &mut pn);
                let count: usize = (&pn)[0];
                if res2 || count > bound
                { (&mut pres)[0] = false }
                else
                {
                    let n·: usize = n0.wrapping_sub(1usize).wrapping_add(count);
                    (&mut pn)[0] = n·
                }
            }
        };
        let res0: bool = (&pres)[0];
        let n1: usize = (&pn)[0];
        cond = res0 && n1 > 0usize
    };
    (&pres)[0]
}

fn jump_raw_data_item(input: &[u8], offset: usize) -> usize
{
    let mut poffset: [usize; 1] = [offset; 1usize];
    let mut pn: [usize; 1] = [1usize; 1usize];
    let n: usize = (&pn)[0];
    let mut cond: bool = n > 0usize;
    while
    cond
    {
        let off: usize = (&poffset)[0];
        let off1: usize = jump_header(input, off);
        let s·: (&[u8], &[u8]) = input.split_at(off);
        let _letpattern: (&[u8], &[u8]) =
            {
                let s1: &[u8] = s·.0;
                let s2: &[u8] = s·.1;
                (s1,s2)
            };
        let input·: &[u8] =
            {
                let _input1: &[u8] = _letpattern.0;
                let input23: &[u8] = _letpattern.1;
                let consumed: usize = off1.wrapping_sub(off);
                let _letpattern1: (&[u8], &[u8]) = input23.split_at(consumed);
                let _letpattern10: (&[u8], &[u8]) =
                    {
                        let s1: &[u8] = _letpattern1.0;
                        let s2: &[u8] = _letpattern1.1;
                        (s1,s2)
                    };
                let _letpattern11: (&[u8], &[u8]) =
                    {
                        let left: &[u8] = _letpattern10.0;
                        let right: &[u8] = _letpattern10.1;
                        (left,right)
                    };
                let input2: &[u8] = _letpattern11.0;
                let _input3: &[u8] = _letpattern11.1;
                input2
            };
        let x: header = read_header(input·);
        let b: initial_byte_t = x.fst;
        let off10: usize =
            if
            b.major_type == cbor_major_type_byte_string
            ||
            b.major_type == cbor_major_type_text_string
            {
                let b0: initial_byte_t = x.fst;
                let l: long_argument = x.snd;
                off1.wrapping_add(argument_as_uint64(b0, l) as usize)
            }
            else
            { off1.wrapping_add(0usize) };
        (&mut poffset)[0] = off10;
        let s·0: (&[u8], &[u8]) = input.split_at(off);
        let _letpattern0: (&[u8], &[u8]) =
            {
                let s1: &[u8] = s·0.0;
                let s2: &[u8] = s·0.1;
                (s1,s2)
            };
        let input1: &[u8] =
            {
                let _input1: &[u8] = _letpattern0.0;
                let input23: &[u8] = _letpattern0.1;
                let consumed: usize = off10.wrapping_sub(off);
                let _letpattern1: (&[u8], &[u8]) = input23.split_at(consumed);
                let _letpattern10: (&[u8], &[u8]) =
                    {
                        let s1: &[u8] = _letpattern1.0;
                        let s2: &[u8] = _letpattern1.1;
                        (s1,s2)
                    };
                let _letpattern11: (&[u8], &[u8]) =
                    {
                        let left: &[u8] = _letpattern10.0;
                        let right: &[u8] = _letpattern10.1;
                        (left,right)
                    };
                let input2: &[u8] = _letpattern11.0;
                let _input3: &[u8] = _letpattern11.1;
                input2
            };
        let n0: usize = (&pn)[0];
        let unused: usize = input.len().wrapping_sub(off10);
        crate::lowstar::ignore::ignore::<usize>(unused);
        let count: usize = jump_recursive_step_count_leaf(input1);
        (&mut pn)[0] = n0.wrapping_sub(1usize).wrapping_add(count);
        let n1: usize = (&pn)[0];
        cond = n1 > 0usize
    };
    (&poffset)[0]
}

fn cbor_read <'a>(input: &'a [u8]) -> cbor_raw <'a>
{
    let mut ph: [header; 1] =
        [header
            {
                fst:
                initial_byte_t { major_type: cbor_major_type_simple_value, additional_info: 0u8 },
                snd: long_argument::LongArgumentOther
            };
            1usize];
    let i: usize = jump_header(input, 0usize);
    let s: (&[u8], &[u8]) = input.split_at(i);
    let _letpattern: (&[u8], &[u8]) =
        {
            let s1: &[u8] = s.0;
            let s2: &[u8] = s.1;
            (s1,s2)
        };
    let _letpattern0: (&[u8], &[u8]) =
        {
            let input1: &[u8] = _letpattern.0;
            let input2: &[u8] = _letpattern.1;
            (input1,input2)
        };
    let pc: &[u8] =
        {
            let ph1: &[u8] = _letpattern0.0;
            let outc: &[u8] = _letpattern0.1;
            let h: header = read_header(ph1);
            (&mut ph)[0] = h;
            outc
        };
    let h: header = (&ph)[0];
    let typ: u8 = h.fst.major_type;
    if typ == cbor_major_type_uint64 || typ == cbor_major_type_neg_int64
    {
        let b: initial_byte_t = h.fst;
        let l: long_argument = h.snd;
        let i0: raw_uint64 =
            match l
            {
                long_argument::LongArgumentU8 { v: v1 } =>
                  raw_uint64 { size: 1u8, value: v1 as u64 },
                long_argument::LongArgumentU16 { v: v1 } =>
                  raw_uint64 { size: 2u8, value: v1 as u64 },
                long_argument::LongArgumentU32 { v: v1 } =>
                  raw_uint64 { size: 3u8, value: v1 as u64 },
                long_argument::LongArgumentU64 { v: v1 } => raw_uint64 { size: 4u8, value: v1 },
                long_argument::LongArgumentOther =>
                  raw_uint64 { size: 0u8, value: b.additional_info as u64 },
                _ => panic!("Incomplete pattern matching")
            };
        let resi: cbor_int =
            cbor_int { cbor_int_type: typ, cbor_int_size: i0.size, cbor_int_value: i0.value };
        cbor_raw::CBOR_Case_Int { v: resi }
    }
    else if typ == cbor_major_type_text_string || typ == cbor_major_type_byte_string
    {
        let b: initial_byte_t = h.fst;
        let l: long_argument = h.snd;
        let i0: raw_uint64 =
            match l
            {
                long_argument::LongArgumentU8 { v: v1 } =>
                  raw_uint64 { size: 1u8, value: v1 as u64 },
                long_argument::LongArgumentU16 { v: v1 } =>
                  raw_uint64 { size: 2u8, value: v1 as u64 },
                long_argument::LongArgumentU32 { v: v1 } =>
                  raw_uint64 { size: 3u8, value: v1 as u64 },
                long_argument::LongArgumentU64 { v: v1 } => raw_uint64 { size: 4u8, value: v1 },
                long_argument::LongArgumentOther =>
                  raw_uint64 { size: 0u8, value: b.additional_info as u64 },
                _ => panic!("Incomplete pattern matching")
            };
        let ress: cbor_string =
            cbor_string { cbor_string_type: typ, cbor_string_size: i0.size, cbor_string_ptr: pc };
        cbor_raw::CBOR_Case_String { v: ress }
    }
    else if typ == cbor_major_type_tagged
    {
        let b: initial_byte_t = h.fst;
        let l: long_argument = h.snd;
        let tag: raw_uint64 =
            match l
            {
                long_argument::LongArgumentU8 { v: v1 } =>
                  raw_uint64 { size: 1u8, value: v1 as u64 },
                long_argument::LongArgumentU16 { v: v1 } =>
                  raw_uint64 { size: 2u8, value: v1 as u64 },
                long_argument::LongArgumentU32 { v: v1 } =>
                  raw_uint64 { size: 3u8, value: v1 as u64 },
                long_argument::LongArgumentU64 { v: v1 } => raw_uint64 { size: 4u8, value: v1 },
                long_argument::LongArgumentOther =>
                  raw_uint64 { size: 0u8, value: b.additional_info as u64 },
                _ => panic!("Incomplete pattern matching")
            };
        let rest: cbor_serialized =
            cbor_serialized { cbor_serialized_header: tag, cbor_serialized_payload: pc };
        cbor_raw::CBOR_Case_Serialized_Tagged { v: rest }
    }
    else if typ == cbor_major_type_array
    {
        let b: initial_byte_t = h.fst;
        let l: long_argument = h.snd;
        let len: raw_uint64 =
            match l
            {
                long_argument::LongArgumentU8 { v: v1 } =>
                  raw_uint64 { size: 1u8, value: v1 as u64 },
                long_argument::LongArgumentU16 { v: v1 } =>
                  raw_uint64 { size: 2u8, value: v1 as u64 },
                long_argument::LongArgumentU32 { v: v1 } =>
                  raw_uint64 { size: 3u8, value: v1 as u64 },
                long_argument::LongArgumentU64 { v: v1 } => raw_uint64 { size: 4u8, value: v1 },
                long_argument::LongArgumentOther =>
                  raw_uint64 { size: 0u8, value: b.additional_info as u64 },
                _ => panic!("Incomplete pattern matching")
            };
        let resa: cbor_serialized =
            cbor_serialized { cbor_serialized_header: len, cbor_serialized_payload: pc };
        cbor_raw::CBOR_Case_Serialized_Array { v: resa }
    }
    else if typ == cbor_major_type_map
    {
        let b: initial_byte_t = h.fst;
        let l: long_argument = h.snd;
        let len: raw_uint64 =
            match l
            {
                long_argument::LongArgumentU8 { v: v1 } =>
                  raw_uint64 { size: 1u8, value: v1 as u64 },
                long_argument::LongArgumentU16 { v: v1 } =>
                  raw_uint64 { size: 2u8, value: v1 as u64 },
                long_argument::LongArgumentU32 { v: v1 } =>
                  raw_uint64 { size: 3u8, value: v1 as u64 },
                long_argument::LongArgumentU64 { v: v1 } => raw_uint64 { size: 4u8, value: v1 },
                long_argument::LongArgumentOther =>
                  raw_uint64 { size: 0u8, value: b.additional_info as u64 },
                _ => panic!("Incomplete pattern matching")
            };
        let resa: cbor_serialized =
            cbor_serialized { cbor_serialized_header: len, cbor_serialized_payload: pc };
        cbor_raw::CBOR_Case_Serialized_Map { v: resa }
    }
    else
    {
        let b: initial_byte_t = h.fst;
        let l: long_argument = h.snd;
        let i0: u8 =
            match l
            {
                long_argument::LongArgumentOther => b.additional_info,
                long_argument::LongArgumentSimpleValue { v: v1 } => v1,
                _ => panic!("Incomplete pattern matching")
            };
        cbor_raw::CBOR_Case_Simple { v: i0 }
    }
}

fn cbor_parse <'a>(input: &'a [u8], len: usize) -> cbor_raw <'a>
{
    let s·: (&[u8], &[u8]) = input.split_at(0usize);
    let _letpattern: (&[u8], &[u8]) =
        {
            let s1: &[u8] = s·.0;
            let s2: &[u8] = s·.1;
            (s1,s2)
        };
    let input1: &[u8] =
        {
            let _input1: &[u8] = _letpattern.0;
            let input23: &[u8] = _letpattern.1;
            let consumed: usize = len.wrapping_sub(0usize);
            let _letpattern1: (&[u8], &[u8]) = input23.split_at(consumed);
            let _letpattern10: (&[u8], &[u8]) =
                {
                    let s1: &[u8] = _letpattern1.0;
                    let s2: &[u8] = _letpattern1.1;
                    (s1,s2)
                };
            let _letpattern11: (&[u8], &[u8]) =
                {
                    let left: &[u8] = _letpattern10.0;
                    let right: &[u8] = _letpattern10.1;
                    (left,right)
                };
            let input2: &[u8] = _letpattern11.0;
            let _input3: &[u8] = _letpattern11.1;
            input2
        };
    cbor_read(input1)
}

fn cbor_match_serialized_tagged_get_payload <'a>(c: cbor_serialized <'a>) -> cbor_raw <'a>
{ cbor_read(c.cbor_serialized_payload) }

fn cbor_serialized_array_item <'a>(c: cbor_serialized <'a>, i: u64) -> cbor_raw <'a>
{
    let j: usize = i as usize;
    let mut pi: [usize; 1] = [0usize; 1usize];
    let mut pres: [&[u8]; 1] = [c.cbor_serialized_payload; 1usize];
    let i1: usize = (&pi)[0];
    let mut cond: bool = i1 < j;
    while
    cond
    {
        let res: &[u8] = (&pres)[0];
        let i10: usize = (&pi)[0];
        let i2: usize = jump_raw_data_item(res, 0usize);
        let s: (&[u8], &[u8]) = res.split_at(i2);
        let _letpattern: (&[u8], &[u8]) =
            {
                let s1: &[u8] = s.0;
                let s2: &[u8] = s.1;
                (s1,s2)
            };
        let _letpattern0: (&[u8], &[u8]) =
            {
                let input1: &[u8] = _letpattern.0;
                let input2: &[u8] = _letpattern.1;
                (input1,input2)
            };
        let _letpattern1: (&[u8], &[u8]) =
            {
                let input1: &[u8] = _letpattern0.0;
                let input2: &[u8] = _letpattern0.1;
                (input1,input2)
            };
        let res2: &[u8] =
            {
                let _input1: &[u8] = _letpattern1.0;
                let input2: &[u8] = _letpattern1.1;
                input2
            };
        (&mut pi)[0] = i10.wrapping_add(1usize);
        (&mut pres)[0] = res2;
        let i11: usize = (&pi)[0];
        cond = i11 < j
    };
    let res: &[u8] = (&pres)[0];
    let i10: usize = jump_raw_data_item(res, 0usize);
    let s: (&[u8], &[u8]) = res.split_at(i10);
    let _letpattern: (&[u8], &[u8]) =
        {
            let s1: &[u8] = s.0;
            let s2: &[u8] = s.1;
            (s1,s2)
        };
    let _letpattern0: (&[u8], &[u8]) =
        {
            let input1: &[u8] = _letpattern.0;
            let input2: &[u8] = _letpattern.1;
            (input1,input2)
        };
    let _letpattern1: (&[u8], &[u8]) =
        {
            let input1: &[u8] = _letpattern0.0;
            let input2: &[u8] = _letpattern0.1;
            (input1,input2)
        };
    let elt: &[u8] =
        {
            let input1: &[u8] = _letpattern1.0;
            let _input2: &[u8] = _letpattern1.1;
            input1
        };
    cbor_read(elt)
}

fn cbor_serialized_array_iterator_init <'a>(c: cbor_serialized <'a>) ->
    cbor_raw_serialized_iterator
    <'a>
{
    cbor_raw_serialized_iterator
    { s: c.cbor_serialized_payload, len: c.cbor_serialized_header.value }
}

fn cbor_serialized_array_iterator_is_empty(c: cbor_raw_serialized_iterator) -> bool
{ c.len == 0u64 }

fn cbor_serialized_array_iterator_length(c: cbor_raw_serialized_iterator) -> u64 { c.len }

#[derive(PartialEq, Clone, Copy)]
enum cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_tags
{
    CBOR_Raw_Iterator_Slice,
    CBOR_Raw_Iterator_Serialized
}

#[derive(PartialEq, Clone, Copy)]
pub enum cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>
{
    CBOR_Raw_Iterator_Slice { _0: &'a [cbor_raw <'a>] },
    CBOR_Raw_Iterator_Serialized { _0: cbor_raw_serialized_iterator <'a> }
}

fn cbor_serialized_array_iterator_next <'b, 'a>(
    pi: &'b mut [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>],
    i: cbor_raw_serialized_iterator <'a>
) ->
    cbor_raw
    <'a>
{
    let i1: usize = jump_raw_data_item(i.s, 0usize);
    let s: (&[u8], &[u8]) = (i.s).split_at(i1);
    let _letpattern: (&[u8], &[u8]) =
        {
            let s1: &[u8] = s.0;
            let s2: &[u8] = s.1;
            (s1,s2)
        };
    let _letpattern0: (&[u8], &[u8]) =
        {
            let input1: &[u8] = _letpattern.0;
            let input2: &[u8] = _letpattern.1;
            (input1,input2)
        };
    let _letpattern1: (&[u8], &[u8]) =
        {
            let input1: &[u8] = _letpattern0.0;
            let input2: &[u8] = _letpattern0.1;
            (input1,input2)
        };
    let s1: &[u8] = _letpattern1.0;
    let s2: &[u8] = _letpattern1.1;
    let res: cbor_raw = cbor_read(s1);
    let i·: cbor_raw_serialized_iterator =
        cbor_raw_serialized_iterator { s: s2, len: (i.len).wrapping_sub(1u64) };
    pi[0] =
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized { _0: i· };
    res
}

fn cbor_serialized_array_iterator_truncate <'a>(c: cbor_raw_serialized_iterator <'a>, len: u64) ->
    cbor_raw_serialized_iterator
    <'a>
{ cbor_raw_serialized_iterator { s: c.s, len } }

fn cbor_serialized_map_iterator_init <'a>(c: cbor_serialized <'a>) ->
    cbor_raw_serialized_iterator
    <'a>
{
    cbor_raw_serialized_iterator
    { s: c.cbor_serialized_payload, len: c.cbor_serialized_header.value }
}

fn cbor_serialized_map_iterator_is_empty(c: cbor_raw_serialized_iterator) -> bool
{ c.len == 0u64 }

#[derive(PartialEq, Clone, Copy)]
pub enum cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>
{
    CBOR_Raw_Iterator_Slice { _0: &'a [cbor_map_entry <'a>] },
    CBOR_Raw_Iterator_Serialized { _0: cbor_raw_serialized_iterator <'a> }
}

fn cbor_serialized_map_iterator_next <'b, 'a>(
    pi: &'b mut [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>],
    i: cbor_raw_serialized_iterator <'a>
) ->
    cbor_map_entry
    <'a>
{
    let off1: usize = jump_raw_data_item(i.s, 0usize);
    let i1: usize = jump_raw_data_item(i.s, off1);
    let s: (&[u8], &[u8]) = (i.s).split_at(i1);
    let _letpattern: (&[u8], &[u8]) =
        {
            let s1: &[u8] = s.0;
            let s2: &[u8] = s.1;
            (s1,s2)
        };
    let _letpattern0: (&[u8], &[u8]) =
        {
            let input1: &[u8] = _letpattern.0;
            let input2: &[u8] = _letpattern.1;
            (input1,input2)
        };
    let _letpattern1: (&[u8], &[u8]) =
        {
            let input1: &[u8] = _letpattern0.0;
            let input2: &[u8] = _letpattern0.1;
            (input1,input2)
        };
    let s1: &[u8] = _letpattern1.0;
    let s2: &[u8] = _letpattern1.1;
    let i10: usize = jump_raw_data_item(s1, 0usize);
    let s0: (&[u8], &[u8]) = s1.split_at(i10);
    let _letpattern10: (&[u8], &[u8]) =
        {
            let s11: &[u8] = s0.0;
            let s21: &[u8] = s0.1;
            (s11,s21)
        };
    let _letpattern11: (&[u8], &[u8]) =
        {
            let input1: &[u8] = _letpattern10.0;
            let input2: &[u8] = _letpattern10.1;
            (input1,input2)
        };
    let _letpattern12: (&[u8], &[u8]) =
        {
            let input1: &[u8] = _letpattern11.0;
            let input2: &[u8] = _letpattern11.1;
            (input1,input2)
        };
    let res: cbor_map_entry =
        {
            let s11: &[u8] = _letpattern12.0;
            let s21: &[u8] = _letpattern12.1;
            let res1: cbor_raw = cbor_read(s11);
            let res2: cbor_raw = cbor_read(s21);
            cbor_map_entry { cbor_map_entry_key: res1, cbor_map_entry_value: res2 }
        };
    let i·: cbor_raw_serialized_iterator =
        cbor_raw_serialized_iterator { s: s2, len: (i.len).wrapping_sub(1u64) };
    pi[0] =
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
        { _0: i· };
    res
}

fn cbor_match_tagged_get_payload <'a>(c: cbor_raw <'a>) -> cbor_raw <'a>
{
    match c
    {
        cbor_raw::CBOR_Case_Serialized_Tagged { v: cs } =>
          cbor_match_serialized_tagged_get_payload(cs),
        cbor_raw::CBOR_Case_Tagged { v: ct } => ct.cbor_tagged_ptr[0],
        _ => panic!("Incomplete pattern matching")
    }
}

fn cbor_array_item <'a>(c: cbor_raw <'a>, i: u64) -> cbor_raw <'a>
{
    match c
    {
        cbor_raw::CBOR_Case_Serialized_Array { v: c· } => cbor_serialized_array_item(c·, i),
        cbor_raw::CBOR_Case_Array { v: c· } => c·.cbor_array_ptr[i as usize],
        _ => panic!("Incomplete pattern matching")
    }
}

fn cbor_array_iterator_init <'a>(c: cbor_raw <'a>) ->
    cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{
    match c
    {
        cbor_raw::CBOR_Case_Serialized_Array { v: c· } =>
          {
              let i·: cbor_raw_serialized_iterator = cbor_serialized_array_iterator_init(c·);
              cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized
              { _0: i· }
          },
        cbor_raw::CBOR_Case_Array { v: c· } =>
          {
              let i: &[cbor_raw] = c·.cbor_array_ptr;
              cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice { _0: i }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

fn cbor_array_iterator_is_empty(c: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw) -> bool
{
    match c
    {
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice { _0: c· } =>
          c·.len() == 0usize,
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized { _0: c· } =>
          cbor_serialized_array_iterator_is_empty(c·),
        _ => panic!("Incomplete pattern matching")
    }
}

pub(crate) fn cbor_array_iterator_length(c: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw) ->
    u64
{
    match c
    {
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice { _0: c· } =>
          c·.len() as u64,
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized { _0: c· } =>
          cbor_serialized_array_iterator_length(c·),
        _ => panic!("Incomplete pattern matching")
    }
}

fn cbor_array_iterator_next <'b, 'a>(
    pi: &'b mut [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>]
) ->
    cbor_raw
    <'a>
{
    let i0: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = pi[0];
    match i0
    {
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice { _0: i1 } =>
          {
              let res: cbor_raw = i1[0usize];
              let _letpattern: (&[cbor_raw], &[cbor_raw]) = i1.split_at(1usize);
              let s·: &[cbor_raw] =
                  {
                      let _s1: &[cbor_raw] = _letpattern.0;
                      let s2: &[cbor_raw] = _letpattern.1;
                      s2
                  };
              let i11: &[cbor_raw] = s·;
              let i·: &[cbor_raw] = i11;
              pi[0] =
                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice
                  { _0: i· };
              res
          },
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized { _0: i1 } =>
          cbor_serialized_array_iterator_next(pi, i1),
        _ => panic!("Incomplete pattern matching")
    }
}

pub(crate) fn cbor_array_iterator_truncate <'a>(
    c: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>,
    len: u64
) ->
    cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{
    match c
    {
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice { _0: c· } =>
          {
              let s·: (&[cbor_raw], &[cbor_raw]) = c·.split_at(len as usize);
              let _letpattern: (&[cbor_raw], &[cbor_raw]) =
                  {
                      let s11: &[cbor_raw] = s·.0;
                      let s21: &[cbor_raw] = s·.1;
                      (s11,s21)
                  };
              let sl1: &[cbor_raw] = _letpattern.0;
              let _sl2: &[cbor_raw] = _letpattern.1;
              let c1: &[cbor_raw] = sl1;
              let c·1: &[cbor_raw] = c1;
              cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice { _0: c·1 }
          },
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized { _0: c· } =>
          {
              let sres: cbor_raw_serialized_iterator =
                  cbor_serialized_array_iterator_truncate(c·, len);
              cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized
              { _0: sres }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

fn cbor_map_iterator_init <'a>(c: cbor_raw <'a>) ->
    cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
    <'a>
{
    match c
    {
        cbor_raw::CBOR_Case_Serialized_Map { v: c· } =>
          {
              let i·: cbor_raw_serialized_iterator = cbor_serialized_map_iterator_init(c·);
              cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
              { _0: i· }
          },
        cbor_raw::CBOR_Case_Map { v: c· } =>
          {
              let i: &[cbor_map_entry] = c·.cbor_map_ptr;
              cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
              { _0: i }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

fn cbor_map_iterator_is_empty(c: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry) -> bool
{
    match c
    {
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
        { _0: c· }
        => c·.len() == 0usize,
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
        { _0: c· }
        => cbor_serialized_map_iterator_is_empty(c·),
        _ => panic!("Incomplete pattern matching")
    }
}

fn cbor_map_iterator_next <'b, 'a>(
    pi: &'b mut [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>]
) ->
    cbor_map_entry
    <'a>
{
    let i0: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry = pi[0];
    match i0
    {
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice { _0: i1 } =>
          {
              let res: cbor_map_entry = i1[0usize];
              let _letpattern: (&[cbor_map_entry], &[cbor_map_entry]) = i1.split_at(1usize);
              let s·: &[cbor_map_entry] =
                  {
                      let _s1: &[cbor_map_entry] = _letpattern.0;
                      let s2: &[cbor_map_entry] = _letpattern.1;
                      s2
                  };
              let i11: &[cbor_map_entry] = s·;
              let i·: &[cbor_map_entry] = i11;
              pi[0] =
                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
                  { _0: i· };
              res
          },
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
        { _0: i1 }
        => cbor_serialized_map_iterator_next(pi, i1),
        _ => panic!("Incomplete pattern matching")
    }
}

fn
__proj__Mkdtuple2__item___1__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
    pair: header
) ->
    initial_byte_t
{ pair.fst }

fn dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
    t: header
) ->
    initial_byte_t
{
    __proj__Mkdtuple2__item___1__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
        t
    )
}

fn
__proj__Mkdtuple2__item___2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
    pair: header
) ->
    long_argument
{ pair.snd }

fn dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
    t: header
) ->
    long_argument
{
    __proj__Mkdtuple2__item___2__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
        t
    )
}

fn write_header(x: header, out: &mut [u8], offset: usize) -> usize
{
    let xh1: initial_byte_t =
        dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
    let pos·: usize = offset.wrapping_add(1usize);
    let n·: u8 =
        set_bitfield_gen8(
            set_bitfield_gen8(0u8, 0u32, 5u32, xh1.additional_info),
            5u32,
            8u32,
            xh1.major_type
        );
    out[pos·.wrapping_sub(1usize)] = n·;
    let res1: usize = pos·;
    let x2·: long_argument =
        dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
    if xh1.additional_info == additional_info_long_argument_8_bits
    {
        if xh1.major_type == cbor_major_type_simple_value
        {
            let pos·0: usize = res1.wrapping_add(1usize);
            let n·0: u8 =
                match x2·
                {
                    long_argument::LongArgumentSimpleValue { v } => v,
                    _ => panic!("Incomplete pattern matching")
                };
            out[pos·0.wrapping_sub(1usize)] = n·0;
            pos·0
        }
        else
        {
            let pos·0: usize = res1.wrapping_add(1usize);
            let n·0: u8 =
                match x2·
                {
                    long_argument::LongArgumentU8 { v } => v,
                    _ => panic!("Incomplete pattern matching")
                };
            out[pos·0.wrapping_sub(1usize)] = n·0;
            pos·0
        }
    }
    else if xh1.additional_info == additional_info_long_argument_16_bits
    {
        let pos·0: usize = res1.wrapping_add(2usize);
        let lo: u8 =
            match x2·
            {
                long_argument::LongArgumentU16 { v } => v,
                _ => panic!("Incomplete pattern matching")
            }
            as
            u8;
        let hi: u16 =
            match x2·
            {
                long_argument::LongArgumentU16 { v } => v,
                _ => panic!("Incomplete pattern matching")
            }.wrapping_div(256u16);
        let pos·1: usize = pos·0.wrapping_sub(1usize);
        let n·0: u8 = hi as u8;
        out[pos·1.wrapping_sub(1usize)] = n·0;
        out[pos·1] = lo;
        pos·0
    }
    else if xh1.additional_info == additional_info_long_argument_32_bits
    {
        let pos·0: usize = res1.wrapping_add(4usize);
        let lo: u8 =
            match x2·
            {
                long_argument::LongArgumentU32 { v } => v,
                _ => panic!("Incomplete pattern matching")
            }
            as
            u8;
        let hi: u32 =
            match x2·
            {
                long_argument::LongArgumentU32 { v } => v,
                _ => panic!("Incomplete pattern matching")
            }.wrapping_div(256u32);
        let pos·1: usize = pos·0.wrapping_sub(1usize);
        let lo1: u8 = hi as u8;
        let hi1: u32 = hi.wrapping_div(256u32);
        let pos·2: usize = pos·1.wrapping_sub(1usize);
        let lo2: u8 = hi1 as u8;
        let hi2: u32 = hi1.wrapping_div(256u32);
        let pos·3: usize = pos·2.wrapping_sub(1usize);
        let n·0: u8 = hi2 as u8;
        out[pos·3.wrapping_sub(1usize)] = n·0;
        out[pos·3] = lo2;
        out[pos·2] = lo1;
        out[pos·1] = lo;
        pos·0
    }
    else if xh1.additional_info == additional_info_long_argument_64_bits
    {
        let pos·0: usize = res1.wrapping_add(8usize);
        let lo: u8 =
            match x2·
            {
                long_argument::LongArgumentU64 { v } => v,
                _ => panic!("Incomplete pattern matching")
            }
            as
            u8;
        let hi: u64 =
            match x2·
            {
                long_argument::LongArgumentU64 { v } => v,
                _ => panic!("Incomplete pattern matching")
            }.wrapping_div(256u64);
        let pos·1: usize = pos·0.wrapping_sub(1usize);
        let lo1: u8 = hi as u8;
        let hi1: u64 = hi.wrapping_div(256u64);
        let pos·2: usize = pos·1.wrapping_sub(1usize);
        let lo2: u8 = hi1 as u8;
        let hi2: u64 = hi1.wrapping_div(256u64);
        let pos·3: usize = pos·2.wrapping_sub(1usize);
        let lo3: u8 = hi2 as u8;
        let hi3: u64 = hi2.wrapping_div(256u64);
        let pos·4: usize = pos·3.wrapping_sub(1usize);
        let lo4: u8 = hi3 as u8;
        let hi4: u64 = hi3.wrapping_div(256u64);
        let pos·5: usize = pos·4.wrapping_sub(1usize);
        let lo5: u8 = hi4 as u8;
        let hi5: u64 = hi4.wrapping_div(256u64);
        let pos·6: usize = pos·5.wrapping_sub(1usize);
        let lo6: u8 = hi5 as u8;
        let hi6: u64 = hi5.wrapping_div(256u64);
        let pos·7: usize = pos·6.wrapping_sub(1usize);
        let n·0: u8 = hi6 as u8;
        out[pos·7.wrapping_sub(1usize)] = n·0;
        out[pos·7] = lo6;
        out[pos·6] = lo5;
        out[pos·5] = lo4;
        out[pos·4] = lo3;
        out[pos·3] = lo2;
        out[pos·2] = lo1;
        out[pos·1] = lo;
        pos·0
    }
    else
    { res1 }
}

fn size_header(x: header, out: &mut [usize]) -> bool
{
    let xh1: initial_byte_t =
        dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
    let capacity: usize = out[0];
    let res1: bool =
        if capacity < 1usize
        { false }
        else
        {
            out[0] = capacity.wrapping_sub(1usize);
            true
        };
    if res1
    {
        let x2·: long_argument =
            dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
        crate::lowstar::ignore::ignore::<long_argument>(x2·);
        if xh1.additional_info == additional_info_long_argument_8_bits
        {
            let capacity0: usize = out[0];
            if capacity0 < 1usize
            { false }
            else
            {
                out[0] = capacity0.wrapping_sub(1usize);
                true
            }
        }
        else if xh1.additional_info == additional_info_long_argument_16_bits
        {
            let capacity0: usize = out[0];
            if capacity0 < 2usize
            { false }
            else
            {
                out[0] = capacity0.wrapping_sub(2usize);
                true
            }
        }
        else if xh1.additional_info == additional_info_long_argument_32_bits
        {
            let capacity0: usize = out[0];
            if capacity0 < 4usize
            { false }
            else
            {
                out[0] = capacity0.wrapping_sub(4usize);
                true
            }
        }
        else if xh1.additional_info == additional_info_long_argument_64_bits
        {
            let capacity0: usize = out[0];
            if capacity0 < 8usize
            { false }
            else
            {
                out[0] = capacity0.wrapping_sub(8usize);
                true
            }
        }
        else
        { true }
    }
    else
    { false }
}

fn cbor_raw_get_header(xl: cbor_raw) -> header
{
    match xl
    {
        cbor_raw::CBOR_Case_Int { .. } =>
          {
              let _letpattern: cbor_raw = xl;
              let ty: u8 =
                  match _letpattern
                  {
                      cbor_raw::CBOR_Case_Int { v: c· } => c·.cbor_int_type,
                      _ => panic!("Incomplete pattern matching")
                  };
              let _letpattern0: cbor_raw = xl;
              let v: raw_uint64 =
                  match _letpattern0
                  {
                      cbor_raw::CBOR_Case_Int { v: c· } =>
                        raw_uint64 { size: c·.cbor_int_size, value: c·.cbor_int_value },
                      _ => panic!("Incomplete pattern matching")
                  };
              raw_uint64_as_argument(ty, v)
          },
        cbor_raw::CBOR_Case_String { .. } =>
          {
              let _letpattern: cbor_raw = xl;
              let ty: u8 =
                  match _letpattern
                  {
                      cbor_raw::CBOR_Case_String { v: c· } => c·.cbor_string_type,
                      _ => panic!("Incomplete pattern matching")
                  };
              let _letpattern0: cbor_raw = xl;
              let len: raw_uint64 =
                  match _letpattern0
                  {
                      cbor_raw::CBOR_Case_String { v: c· } =>
                        raw_uint64
                        { size: c·.cbor_string_size, value: (c·.cbor_string_ptr).len() as u64 },
                      _ => panic!("Incomplete pattern matching")
                  };
              raw_uint64_as_argument(ty, len)
          },
        cbor_raw::CBOR_Case_Tagged { .. } =>
          {
              let tag: raw_uint64 =
                  match xl
                  {
                      cbor_raw::CBOR_Case_Tagged { v: c· } => c·.cbor_tagged_tag,
                      cbor_raw::CBOR_Case_Serialized_Tagged { v: c· } => c·.cbor_serialized_header,
                      _ => panic!("Incomplete pattern matching")
                  };
              raw_uint64_as_argument(cbor_major_type_tagged, tag)
          },
        cbor_raw::CBOR_Case_Serialized_Tagged { .. } =>
          {
              let tag: raw_uint64 =
                  match xl
                  {
                      cbor_raw::CBOR_Case_Tagged { v: c· } => c·.cbor_tagged_tag,
                      cbor_raw::CBOR_Case_Serialized_Tagged { v: c· } => c·.cbor_serialized_header,
                      _ => panic!("Incomplete pattern matching")
                  };
              raw_uint64_as_argument(cbor_major_type_tagged, tag)
          },
        cbor_raw::CBOR_Case_Array { .. } =>
          {
              let len: raw_uint64 =
                  match xl
                  {
                      cbor_raw::CBOR_Case_Array { v: c· } =>
                        raw_uint64
                        {
                            size: c·.cbor_array_length_size,
                            value: (c·.cbor_array_ptr).len() as u64
                        },
                      cbor_raw::CBOR_Case_Serialized_Array { v: c· } => c·.cbor_serialized_header,
                      _ => panic!("Incomplete pattern matching")
                  };
              raw_uint64_as_argument(cbor_major_type_array, len)
          },
        cbor_raw::CBOR_Case_Serialized_Array { .. } =>
          {
              let len: raw_uint64 =
                  match xl
                  {
                      cbor_raw::CBOR_Case_Array { v: c· } =>
                        raw_uint64
                        {
                            size: c·.cbor_array_length_size,
                            value: (c·.cbor_array_ptr).len() as u64
                        },
                      cbor_raw::CBOR_Case_Serialized_Array { v: c· } => c·.cbor_serialized_header,
                      _ => panic!("Incomplete pattern matching")
                  };
              raw_uint64_as_argument(cbor_major_type_array, len)
          },
        cbor_raw::CBOR_Case_Map { .. } =>
          {
              let len: raw_uint64 =
                  match xl
                  {
                      cbor_raw::CBOR_Case_Map { v: c· } =>
                        raw_uint64
                        { size: c·.cbor_map_length_size, value: (c·.cbor_map_ptr).len() as u64 },
                      cbor_raw::CBOR_Case_Serialized_Map { v: c· } => c·.cbor_serialized_header,
                      _ => panic!("Incomplete pattern matching")
                  };
              raw_uint64_as_argument(cbor_major_type_map, len)
          },
        cbor_raw::CBOR_Case_Serialized_Map { .. } =>
          {
              let len: raw_uint64 =
                  match xl
                  {
                      cbor_raw::CBOR_Case_Map { v: c· } =>
                        raw_uint64
                        { size: c·.cbor_map_length_size, value: (c·.cbor_map_ptr).len() as u64 },
                      cbor_raw::CBOR_Case_Serialized_Map { v: c· } => c·.cbor_serialized_header,
                      _ => panic!("Incomplete pattern matching")
                  };
              raw_uint64_as_argument(cbor_major_type_map, len)
          },
        cbor_raw::CBOR_Case_Simple { .. } =>
          {
              let _letpattern: cbor_raw = xl;
              let v: u8 =
                  match _letpattern
                  {
                      cbor_raw::CBOR_Case_Simple { v: res } => res,
                      _ => panic!("Incomplete pattern matching")
                  };
              simple_value_as_argument(v)
          },
        _ => panic!("Incomplete pattern matching")
    }
}

fn cbor_raw_with_perm_get_header(xl: cbor_raw) -> header { cbor_raw_get_header(xl) }

#[derive(PartialEq, Clone, Copy)]
enum
option__LowParse_Pulse_Base_with_perm·Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw
<'a>
{
    None,
    Some { v: &'a [cbor_raw <'a>] }
}

#[derive(PartialEq, Clone, Copy)]
enum
option__LowParse_Pulse_Base_with_perm·Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry
<'a>
{
    None,
    Some { v: &'a [cbor_map_entry <'a>] }
}

pub(crate) fn ser·(x·: cbor_raw, out: &mut [u8], offset: usize) -> usize
{
    let xh1: header = cbor_raw_with_perm_get_header(x·);
    let res1: usize = write_header(xh1, out, offset);
    let b: initial_byte_t = xh1.fst;
    if b.major_type == cbor_major_type_byte_string || b.major_type == cbor_major_type_text_string
    {
        let _letpattern: cbor_raw = x·;
        let x2·: &[u8] =
            match _letpattern
            {
                cbor_raw::CBOR_Case_String { v: c· } => c·.cbor_string_ptr,
                _ => panic!("Incomplete pattern matching")
            };
        let length: usize = x2·.len();
        let _letpattern0: (&mut [u8], &mut [u8]) = out.split_at_mut(res1);
        let _sp11: &[u8] = _letpattern0.0;
        let sp12: &mut [u8] = _letpattern0.1;
        let _letpattern1: (&mut [u8], &mut [u8]) = sp12.split_at_mut(length);
        let sp21: &mut [u8] = _letpattern1.0;
        let _sp22: &[u8] = _letpattern1.1;
        sp21.copy_from_slice(x2·);
        res1.wrapping_add(length)
    }
    else
    {
        let b0: initial_byte_t = xh1.fst;
        if b0.major_type == cbor_major_type_array
        {
            if match x· { cbor_raw::CBOR_Case_Array { .. } => true, _ => false }
            {
                let x2·: cbor_raw = x·;
                let a: &[cbor_raw] =
                    match
                    match x2·
                    {
                        cbor_raw::CBOR_Case_Array { v: a } =>
                          option__LowParse_Pulse_Base_with_perm·Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw::Some
                          { v: a.cbor_array_ptr },
                        _ =>
                          option__LowParse_Pulse_Base_with_perm·Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw::None
                    }
                    {
                        option__LowParse_Pulse_Base_with_perm·Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw::Some
                        { v }
                        => v,
                        _ => panic!("Incomplete pattern matching")
                    };
                let mut pres: [usize; 1] = [res1; 1usize];
                let mut pi: [usize; 1] = [0usize; 1usize];
                let i: usize = (&pi)[0];
                let mut cond: bool = i < argument_as_uint64(xh1.fst, xh1.snd) as usize;
                while
                cond
                {
                    let i0: usize = (&pi)[0];
                    let off: usize = (&pres)[0];
                    let e: cbor_raw = a[i0];
                    let i·: usize = i0.wrapping_add(1usize);
                    let x2·1: cbor_raw = e;
                    let res: usize = ser·(x2·1, out, off);
                    (&mut pi)[0] = i·;
                    (&mut pres)[0] = res;
                    let i1: usize = (&pi)[0];
                    cond = i1 < argument_as_uint64(xh1.fst, xh1.snd) as usize
                };
                (&pres)[0]
            }
            else
            {
                let _letpattern: cbor_raw = x·;
                let x2·: &[u8] =
                    match _letpattern
                    {
                        cbor_raw::CBOR_Case_Serialized_Array { v: xs } => xs.cbor_serialized_payload,
                        _ => panic!("Incomplete pattern matching")
                    };
                let length: usize = x2·.len();
                let _letpattern0: (&mut [u8], &mut [u8]) = out.split_at_mut(res1);
                let _sp11: &[u8] = _letpattern0.0;
                let sp12: &mut [u8] = _letpattern0.1;
                let _letpattern1: (&mut [u8], &mut [u8]) = sp12.split_at_mut(length);
                let sp21: &mut [u8] = _letpattern1.0;
                let _sp22: &[u8] = _letpattern1.1;
                sp21.copy_from_slice(x2·);
                res1.wrapping_add(length)
            }
        }
        else
        {
            let b1: initial_byte_t = xh1.fst;
            if b1.major_type == cbor_major_type_map
            {
                if match x· { cbor_raw::CBOR_Case_Map { .. } => true, _ => false }
                {
                    let x2·: cbor_raw = x·;
                    let a: &[cbor_map_entry] =
                        match
                        match x2·
                        {
                            cbor_raw::CBOR_Case_Map { v: a } =>
                              option__LowParse_Pulse_Base_with_perm·Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry::Some
                              { v: a.cbor_map_ptr },
                            _ =>
                              option__LowParse_Pulse_Base_with_perm·Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry::None
                        }
                        {
                            option__LowParse_Pulse_Base_with_perm·Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry::Some
                            { v }
                            => v,
                            _ => panic!("Incomplete pattern matching")
                        };
                    let mut pres: [usize; 1] = [res1; 1usize];
                    let mut pi: [usize; 1] = [0usize; 1usize];
                    let i: usize = (&pi)[0];
                    let mut cond: bool = i < argument_as_uint64(xh1.fst, xh1.snd) as usize;
                    while
                    cond
                    {
                        let i0: usize = (&pi)[0];
                        let off: usize = (&pres)[0];
                        let e: cbor_map_entry = a[i0];
                        let i·: usize = i0.wrapping_add(1usize);
                        let x11: cbor_raw = e.cbor_map_entry_key;
                        let res11: usize = ser·(x11, out, off);
                        let x2: cbor_raw = e.cbor_map_entry_value;
                        let res: usize = ser·(x2, out, res11);
                        (&mut pi)[0] = i·;
                        (&mut pres)[0] = res;
                        let i1: usize = (&pi)[0];
                        cond = i1 < argument_as_uint64(xh1.fst, xh1.snd) as usize
                    };
                    (&pres)[0]
                }
                else
                {
                    let _letpattern: cbor_raw = x·;
                    let x2·: &[u8] =
                        match _letpattern
                        {
                            cbor_raw::CBOR_Case_Serialized_Map { v: xs } =>
                              xs.cbor_serialized_payload,
                            _ => panic!("Incomplete pattern matching")
                        };
                    let length: usize = x2·.len();
                    let _letpattern0: (&mut [u8], &mut [u8]) = out.split_at_mut(res1);
                    let _sp11: &[u8] = _letpattern0.0;
                    let sp12: &mut [u8] = _letpattern0.1;
                    let _letpattern1: (&mut [u8], &mut [u8]) = sp12.split_at_mut(length);
                    let sp21: &mut [u8] = _letpattern1.0;
                    let _sp22: &[u8] = _letpattern1.1;
                    sp21.copy_from_slice(x2·);
                    res1.wrapping_add(length)
                }
            }
            else
            {
                let b2: initial_byte_t = xh1.fst;
                if b2.major_type == cbor_major_type_tagged
                {
                    if match x· { cbor_raw::CBOR_Case_Tagged { .. } => true, _ => false }
                    {
                        let _letpattern: cbor_raw = x·;
                        let x2·: cbor_raw =
                            match _letpattern
                            {
                                cbor_raw::CBOR_Case_Tagged { v: tg } => tg.cbor_tagged_ptr[0],
                                _ => panic!("Incomplete pattern matching")
                            };
                        ser·(x2·, out, res1)
                    }
                    else
                    {
                        let _letpattern: cbor_raw = x·;
                        let x2·: &[u8] =
                            match _letpattern
                            {
                                cbor_raw::CBOR_Case_Serialized_Tagged { v: ser } =>
                                  ser.cbor_serialized_payload,
                                _ => panic!("Incomplete pattern matching")
                            };
                        let length: usize = x2·.len();
                        let _letpattern0: (&mut [u8], &mut [u8]) = out.split_at_mut(res1);
                        let _sp11: &[u8] = _letpattern0.0;
                        let sp12: &mut [u8] = _letpattern0.1;
                        let _letpattern1: (&mut [u8], &mut [u8]) = sp12.split_at_mut(length);
                        let sp21: &mut [u8] = _letpattern1.0;
                        let _sp22: &[u8] = _letpattern1.1;
                        sp21.copy_from_slice(x2·);
                        res1.wrapping_add(length)
                    }
                }
                else
                { res1 }
            }
        }
    }
}

fn ser(x1·: cbor_raw, out: &mut [u8], offset: usize) -> usize
{
    let x2·: cbor_raw = x1·;
    ser·(x2·, out, offset)
}

fn cbor_serialize(x: cbor_raw, output: &mut [u8]) -> usize { ser(x, output, 0usize) }

pub(crate) fn siz·(x·: cbor_raw, out: &mut [usize]) -> bool
{
    let xh1: header = cbor_raw_with_perm_get_header(x·);
    let res1: bool = size_header(xh1, out);
    if res1
    {
        let b: initial_byte_t = xh1.fst;
        if
        b.major_type == cbor_major_type_byte_string || b.major_type == cbor_major_type_text_string
        {
            let _letpattern: cbor_raw = x·;
            let x2·: &[u8] =
                match _letpattern
                {
                    cbor_raw::CBOR_Case_String { v: c· } => c·.cbor_string_ptr,
                    _ => panic!("Incomplete pattern matching")
                };
            let length: usize = x2·.len();
            let cur: usize = out[0];
            if cur < length
            { false }
            else
            {
                out[0] = cur.wrapping_sub(length);
                true
            }
        }
        else
        {
            let b0: initial_byte_t = xh1.fst;
            if b0.major_type == cbor_major_type_array
            {
                if match x· { cbor_raw::CBOR_Case_Array { .. } => true, _ => false }
                {
                    let x2·: cbor_raw = x·;
                    let a: &[cbor_raw] =
                        match
                        match x2·
                        {
                            cbor_raw::CBOR_Case_Array { v: a } =>
                              option__LowParse_Pulse_Base_with_perm·Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw::Some
                              { v: a.cbor_array_ptr },
                            _ =>
                              option__LowParse_Pulse_Base_with_perm·Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw::None
                        }
                        {
                            option__LowParse_Pulse_Base_with_perm·Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw::Some
                            { v }
                            => v,
                            _ => panic!("Incomplete pattern matching")
                        };
                    let mut pres: [bool; 1] = [true; 1usize];
                    let mut pi: [usize; 1] = [0usize; 1usize];
                    let res: bool = (&pres)[0];
                    let i: usize = (&pi)[0];
                    let mut cond: bool = res && i < argument_as_uint64(xh1.fst, xh1.snd) as usize;
                    while
                    cond
                    {
                        let i0: usize = (&pi)[0];
                        let e: cbor_raw = a[i0];
                        let x2·1: cbor_raw = e;
                        let res0: bool = siz·(x2·1, out);
                        if res0
                        {
                            let i·: usize = i0.wrapping_add(1usize);
                            (&mut pi)[0] = i·
                        }
                        else
                        { (&mut pres)[0] = false };
                        let res2: bool = (&pres)[0];
                        let i1: usize = (&pi)[0];
                        cond = res2 && i1 < argument_as_uint64(xh1.fst, xh1.snd) as usize
                    };
                    (&pres)[0]
                }
                else
                {
                    let _letpattern: cbor_raw = x·;
                    let x2·: &[u8] =
                        match _letpattern
                        {
                            cbor_raw::CBOR_Case_Serialized_Array { v: xs } =>
                              xs.cbor_serialized_payload,
                            _ => panic!("Incomplete pattern matching")
                        };
                    let length: usize = x2·.len();
                    let cur: usize = out[0];
                    if cur < length
                    { false }
                    else
                    {
                        out[0] = cur.wrapping_sub(length);
                        true
                    }
                }
            }
            else
            {
                let b1: initial_byte_t = xh1.fst;
                if b1.major_type == cbor_major_type_map
                {
                    if match x· { cbor_raw::CBOR_Case_Map { .. } => true, _ => false }
                    {
                        let x2·: cbor_raw = x·;
                        let a: &[cbor_map_entry] =
                            match
                            match x2·
                            {
                                cbor_raw::CBOR_Case_Map { v: a } =>
                                  option__LowParse_Pulse_Base_with_perm·Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry::Some
                                  { v: a.cbor_map_ptr },
                                _ =>
                                  option__LowParse_Pulse_Base_with_perm·Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry::None
                            }
                            {
                                option__LowParse_Pulse_Base_with_perm·Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry::Some
                                { v }
                                => v,
                                _ => panic!("Incomplete pattern matching")
                            };
                        let mut pres: [bool; 1] = [true; 1usize];
                        let mut pi: [usize; 1] = [0usize; 1usize];
                        let res: bool = (&pres)[0];
                        let i: usize = (&pi)[0];
                        let mut cond: bool =
                            res && i < argument_as_uint64(xh1.fst, xh1.snd) as usize;
                        while
                        cond
                        {
                            let i0: usize = (&pi)[0];
                            let e: cbor_map_entry = a[i0];
                            let x11: cbor_raw = e.cbor_map_entry_key;
                            let res11: bool = siz·(x11, out);
                            let res0: bool =
                                if res11
                                {
                                    let x2: cbor_raw = e.cbor_map_entry_value;
                                    siz·(x2, out)
                                }
                                else
                                { false };
                            if res0
                            {
                                let i·: usize = i0.wrapping_add(1usize);
                                (&mut pi)[0] = i·
                            }
                            else
                            { (&mut pres)[0] = false };
                            let res2: bool = (&pres)[0];
                            let i1: usize = (&pi)[0];
                            cond = res2 && i1 < argument_as_uint64(xh1.fst, xh1.snd) as usize
                        };
                        (&pres)[0]
                    }
                    else
                    {
                        let _letpattern: cbor_raw = x·;
                        let x2·: &[u8] =
                            match _letpattern
                            {
                                cbor_raw::CBOR_Case_Serialized_Map { v: xs } =>
                                  xs.cbor_serialized_payload,
                                _ => panic!("Incomplete pattern matching")
                            };
                        let length: usize = x2·.len();
                        let cur: usize = out[0];
                        if cur < length
                        { false }
                        else
                        {
                            out[0] = cur.wrapping_sub(length);
                            true
                        }
                    }
                }
                else
                {
                    let b2: initial_byte_t = xh1.fst;
                    if b2.major_type == cbor_major_type_tagged
                    {
                        if match x· { cbor_raw::CBOR_Case_Tagged { .. } => true, _ => false }
                        {
                            let _letpattern: cbor_raw = x·;
                            let x2·: cbor_raw =
                                match _letpattern
                                {
                                    cbor_raw::CBOR_Case_Tagged { v: tg } => tg.cbor_tagged_ptr[0],
                                    _ => panic!("Incomplete pattern matching")
                                };
                            siz·(x2·, out)
                        }
                        else
                        {
                            let _letpattern: cbor_raw = x·;
                            let x2·: &[u8] =
                                match _letpattern
                                {
                                    cbor_raw::CBOR_Case_Serialized_Tagged { v: ser1 } =>
                                      ser1.cbor_serialized_payload,
                                    _ => panic!("Incomplete pattern matching")
                                };
                            let length: usize = x2·.len();
                            let cur: usize = out[0];
                            if cur < length
                            { false }
                            else
                            {
                                out[0] = cur.wrapping_sub(length);
                                true
                            }
                        }
                    }
                    else
                    { true }
                }
            }
        }
    }
    else
    { false }
}

fn siz(x1·: cbor_raw, out: &mut [usize]) -> bool
{
    let x2·: cbor_raw = x1·;
    siz·(x2·, out)
}

fn cbor_size(x: cbor_raw, bound: usize) -> usize
{
    let mut output: [usize; 1] = [bound; 1usize];
    let res: bool = siz(x, &mut output);
    if res
    {
        let rem: usize = (&output)[0];
        bound.wrapping_sub(rem)
    }
    else
    { 0usize }
}

fn impl_major_type(x: cbor_raw) -> u8
{
    match x
    {
        cbor_raw::CBOR_Case_Simple { .. } => cbor_major_type_simple_value,
        cbor_raw::CBOR_Case_Int { .. } =>
          {
              let _letpattern: cbor_raw = x;
              match _letpattern
              {
                  cbor_raw::CBOR_Case_Int { v: c· } => c·.cbor_int_type,
                  _ => panic!("Incomplete pattern matching")
              }
          },
        cbor_raw::CBOR_Case_String { .. } =>
          {
              let _letpattern: cbor_raw = x;
              match _letpattern
              {
                  cbor_raw::CBOR_Case_String { v: c· } => c·.cbor_string_type,
                  _ => panic!("Incomplete pattern matching")
              }
          },
        cbor_raw::CBOR_Case_Tagged { .. } => cbor_major_type_tagged,
        cbor_raw::CBOR_Case_Serialized_Tagged { .. } => cbor_major_type_tagged,
        cbor_raw::CBOR_Case_Array { .. } => cbor_major_type_array,
        cbor_raw::CBOR_Case_Serialized_Array { .. } => cbor_major_type_array,
        cbor_raw::CBOR_Case_Map { .. } => cbor_major_type_map,
        cbor_raw::CBOR_Case_Serialized_Map { .. } => cbor_major_type_map,
        _ => panic!("Incomplete pattern matching")
    }
}

pub(crate) fn impl_check_map_depth_aux(bound: usize, pl: &mut [&[u8]], n1: usize) -> bool
{
    let mut pn: [usize; 1] = [n1; 1usize];
    let mut pres: [bool; 1] = [true; 1usize];
    let res: bool = (&pres)[0];
    let n: usize = (&pn)[0];
    let mut cond: bool = res && n > 0usize;
    while
    cond
    {
        let l: &[u8] = pl[0];
        let n0: usize = (&pn)[0];
        let n·: usize = n0.wrapping_sub(1usize);
        let i: usize = jump_header(l, 0usize);
        let s: (&[u8], &[u8]) = l.split_at(i);
        let _letpattern: (&[u8], &[u8]) =
            {
                let s1: &[u8] = s.0;
                let s2: &[u8] = s.1;
                (s1,s2)
            };
        let _letpattern0: (&[u8], &[u8]) =
            {
                let input1: &[u8] = _letpattern.0;
                let input2: &[u8] = _letpattern.1;
                (input1,input2)
            };
        let _letpattern1: (&[u8], &[u8]) =
            {
                let input1: &[u8] = _letpattern0.0;
                let input2: &[u8] = _letpattern0.1;
                (input1,input2)
            };
        let _letpattern2: (&[u8], &[u8]) =
            {
                let left: &[u8] = _letpattern1.0;
                let right: &[u8] = _letpattern1.1;
                (left,right)
            };
        {
            let hd: &[u8] = _letpattern2.0;
            let tl·: &[u8] = _letpattern2.1;
            let h: header = read_header(hd);
            let b: initial_byte_t = h.fst;
            let i0: usize =
                if
                b.major_type == cbor_major_type_byte_string
                ||
                b.major_type == cbor_major_type_text_string
                {
                    let b0: initial_byte_t = h.fst;
                    let l3: long_argument = h.snd;
                    0usize.wrapping_add(argument_as_uint64(b0, l3) as usize)
                }
                else
                { 0usize };
            let s0: (&[u8], &[u8]) = tl·.split_at(i0);
            let _letpattern10: (&[u8], &[u8]) =
                {
                    let s1: &[u8] = s0.0;
                    let s2: &[u8] = s0.1;
                    (s1,s2)
                };
            let _letpattern11: (&[u8], &[u8]) =
                {
                    let input1: &[u8] = _letpattern10.0;
                    let input2: &[u8] = _letpattern10.1;
                    (input1,input2)
                };
            let _letpattern12: (&[u8], &[u8]) =
                {
                    let input1: &[u8] = _letpattern11.0;
                    let input2: &[u8] = _letpattern11.1;
                    (input1,input2)
                };
            let _letpattern13: (&[u8], &[u8]) =
                {
                    let left: &[u8] = _letpattern12.0;
                    let right: &[u8] = _letpattern12.1;
                    (left,right)
                };
            let tl: &[u8] = _letpattern13.1;
            let m: u8 = get_header_major_type(h);
            if m == cbor_major_type_tagged
            { pl[0] = tl }
            else if m == cbor_major_type_array
            {
                pl[0] = tl;
                (&mut pn)[0] =
                    (argument_as_uint64(
                        dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                            h
                        ),
                        dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                            h
                        )
                    )
                    as
                    usize).wrapping_add(n·)
            }
            else if m == cbor_major_type_map
            {
                if bound == 0usize
                { (&mut pres)[0] = false }
                else
                {
                    pl[0] = tl;
                    let npairs: usize =
                        argument_as_uint64(
                            dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                h
                            ),
                            dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                h
                            )
                        )
                        as
                        usize;
                    let res0: bool =
                        impl_check_map_depth_aux(
                            bound.wrapping_sub(1usize),
                            pl,
                            npairs.wrapping_add(npairs)
                        );
                    if res0 { (&mut pn)[0] = n· } else { (&mut pres)[0] = false }
                }
            }
            else
            {
                pl[0] = tl;
                (&mut pn)[0] = n·
            }
        };
        let res0: bool = (&pres)[0];
        let n2: usize = (&pn)[0];
        cond = res0 && n2 > 0usize
    };
    (&pres)[0]
}

fn impl_check_map_depth(bound: usize, n0: usize, l0: &[u8]) -> bool
{
    let mut pl: [&[u8]; 1] = [l0; 1usize];
    impl_check_map_depth_aux(bound, &mut pl, n0)
}

fn uu___is_None__size_t(projectee: option__size_t) -> bool
{ match projectee { option__size_t::None => true, _ => false } }

fn impl_check_map_depth_opt(bound: option__size_t, n0: usize, l0: &[u8]) -> bool
{
    if uu___is_None__size_t(bound)
    { true }
    else
    {
        impl_check_map_depth(
            match bound
            { option__size_t::Some { v } => v, _ => panic!("Incomplete pattern matching") },
            n0,
            l0
        )
    }
}

fn uu___is_None__bool(projectee: option__bool) -> bool
{ match projectee { option__bool::None => true, _ => false } }

pub(crate) fn impl_check_equiv_map_hd_basic(map_bound: option__size_t, l1: &[u8], l2: &[u8]) ->
    option__bool
{
    let __anf0: bool = false;
    if __anf0
    { option__bool::Some { v: true } }
    else
    {
        let i: usize = jump_header(l1, 0usize);
        let s: (&[u8], &[u8]) = l1.split_at(i);
        let _letpattern: (&[u8], &[u8]) =
            {
                let s1: &[u8] = s.0;
                let s2: &[u8] = s.1;
                (s1,s2)
            };
        let _letpattern0: (&[u8], &[u8]) =
            {
                let input1: &[u8] = _letpattern.0;
                let input2: &[u8] = _letpattern.1;
                (input1,input2)
            };
        let _letpattern1: (&[u8], &[u8]) =
            {
                let input1: &[u8] = _letpattern0.0;
                let input2: &[u8] = _letpattern0.1;
                (input1,input2)
            };
        let ph1: &[u8] =
            {
                let input1: &[u8] = _letpattern1.0;
                let _input2: &[u8] = _letpattern1.1;
                input1
            };
        let h1: header = read_header(ph1);
        let i0: usize = jump_header(l2, 0usize);
        let s0: (&[u8], &[u8]) = l2.split_at(i0);
        let _letpattern2: (&[u8], &[u8]) =
            {
                let s1: &[u8] = s0.0;
                let s2: &[u8] = s0.1;
                (s1,s2)
            };
        let _letpattern3: (&[u8], &[u8]) =
            {
                let input1: &[u8] = _letpattern2.0;
                let input2: &[u8] = _letpattern2.1;
                (input1,input2)
            };
        let _letpattern4: (&[u8], &[u8]) =
            {
                let input1: &[u8] = _letpattern3.0;
                let input2: &[u8] = _letpattern3.1;
                (input1,input2)
            };
        let ph2: &[u8] =
            {
                let input1: &[u8] = _letpattern4.0;
                let _input2: &[u8] = _letpattern4.1;
                input1
            };
        let h2: header = read_header(ph2);
        let mt1: u8 = get_header_major_type(h1);
        let mt2: u8 = get_header_major_type(h2);
        if mt1 == cbor_major_type_map && mt2 == cbor_major_type_map
        {
            if eq_Some_0sz(map_bound)
            { option__bool::None }
            else
            {
                let map_bound·: option__size_t =
                    match map_bound
                    {
                        option__size_t::None => option__size_t::None,
                        option__size_t::Some { v: b } =>
                          option__size_t::Some { v: b.wrapping_sub(1usize) },
                        _ => panic!("Incomplete pattern matching")
                    };
                let nv1: usize =
                    argument_as_uint64(
                        dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                            h1
                        ),
                        dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                            h1
                        )
                    )
                    as
                    usize;
                let nv2: usize =
                    argument_as_uint64(
                        dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                            h2
                        ),
                        dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                            h2
                        )
                    )
                    as
                    usize;
                let i1: usize = jump_raw_data_item(l1, 0usize);
                let s1: (&[u8], &[u8]) = l1.split_at(i1);
                let _letpattern5: (&[u8], &[u8]) =
                    {
                        let s10: &[u8] = s1.0;
                        let s2: &[u8] = s1.1;
                        (s10,s2)
                    };
                let _letpattern6: (&[u8], &[u8]) =
                    {
                        let input1: &[u8] = _letpattern5.0;
                        let input2: &[u8] = _letpattern5.1;
                        (input1,input2)
                    };
                let _letpattern7: (&[u8], &[u8]) =
                    {
                        let input1: &[u8] = _letpattern6.0;
                        let input2: &[u8] = _letpattern6.1;
                        (input1,input2)
                    };
                let map1: &[u8] =
                    {
                        let input1: &[u8] = _letpattern7.0;
                        let _input2: &[u8] = _letpattern7.1;
                        input1
                    };
                let mut ph: [header; 1] = [h1; 1usize];
                let i2: usize = jump_header(map1, 0usize);
                let s2: (&[u8], &[u8]) = map1.split_at(i2);
                let _letpattern8: (&[u8], &[u8]) =
                    {
                        let s10: &[u8] = s2.0;
                        let s20: &[u8] = s2.1;
                        (s10,s20)
                    };
                let _letpattern9: (&[u8], &[u8]) =
                    {
                        let input1: &[u8] = _letpattern8.0;
                        let input2: &[u8] = _letpattern8.1;
                        (input1,input2)
                    };
                let c1: &[u8] =
                    {
                        let ph3: &[u8] = _letpattern9.0;
                        let outc: &[u8] = _letpattern9.1;
                        let h: header = read_header(ph3);
                        (&mut ph)[0] = h;
                        outc
                    };
                let i3: usize = jump_raw_data_item(l2, 0usize);
                let s3: (&[u8], &[u8]) = l2.split_at(i3);
                let _letpattern10: (&[u8], &[u8]) =
                    {
                        let s10: &[u8] = s3.0;
                        let s20: &[u8] = s3.1;
                        (s10,s20)
                    };
                let _letpattern11: (&[u8], &[u8]) =
                    {
                        let input1: &[u8] = _letpattern10.0;
                        let input2: &[u8] = _letpattern10.1;
                        (input1,input2)
                    };
                let _letpattern12: (&[u8], &[u8]) =
                    {
                        let input1: &[u8] = _letpattern11.0;
                        let input2: &[u8] = _letpattern11.1;
                        (input1,input2)
                    };
                let map2: &[u8] =
                    {
                        let input1: &[u8] = _letpattern12.0;
                        let _input2: &[u8] = _letpattern12.1;
                        input1
                    };
                let i4: usize = jump_header(map2, 0usize);
                let s4: (&[u8], &[u8]) = map2.split_at(i4);
                let _letpattern13: (&[u8], &[u8]) =
                    {
                        let s10: &[u8] = s4.0;
                        let s20: &[u8] = s4.1;
                        (s10,s20)
                    };
                let _letpattern14: (&[u8], &[u8]) =
                    {
                        let input1: &[u8] = _letpattern13.0;
                        let input2: &[u8] = _letpattern13.1;
                        (input1,input2)
                    };
                let c2: &[u8] =
                    {
                        let ph3: &[u8] = _letpattern14.0;
                        let outc: &[u8] = _letpattern14.1;
                        let h: header = read_header(ph3);
                        (&mut ph)[0] = h;
                        outc
                    };
                let mut pl: [&[u8]; 1] = [c1; 1usize];
                let mut pn: [usize; 1] = [nv1; 1usize];
                let mut pres: [option__bool; 1] = [option__bool::Some { v: true }; 1usize];
                let n: usize = (&pn)[0];
                let res: option__bool = (&pres)[0];
                let mut cond: bool = n > 0usize && eq_Some_true(res);
                while
                cond
                {
                    let l: &[u8] = (&pl)[0];
                    let n0: usize = (&pn)[0];
                    let n·: usize = n0.wrapping_sub(1usize);
                    let i5: usize = jump_raw_data_item(l, 0usize);
                    let s5: (&[u8], &[u8]) = l.split_at(i5);
                    let _letpattern15: (&[u8], &[u8]) =
                        {
                            let s10: &[u8] = s5.0;
                            let s20: &[u8] = s5.1;
                            (s10,s20)
                        };
                    let _letpattern16: (&[u8], &[u8]) =
                        {
                            let input1: &[u8] = _letpattern15.0;
                            let input2: &[u8] = _letpattern15.1;
                            (input1,input2)
                        };
                    let _letpattern17: (&[u8], &[u8]) =
                        {
                            let input1: &[u8] = _letpattern16.0;
                            let input2: &[u8] = _letpattern16.1;
                            (input1,input2)
                        };
                    let _letpattern18: (&[u8], &[u8]) =
                        {
                            let left: &[u8] = _letpattern17.0;
                            let right: &[u8] = _letpattern17.1;
                            (left,right)
                        };
                    {
                        let lh: &[u8] = _letpattern18.0;
                        let lt: &[u8] = _letpattern18.1;
                        let i6: usize = jump_raw_data_item(lt, 0usize);
                        let s6: (&[u8], &[u8]) = lt.split_at(i6);
                        let _letpattern19: (&[u8], &[u8]) =
                            {
                                let s10: &[u8] = s6.0;
                                let s20: &[u8] = s6.1;
                                (s10,s20)
                            };
                        let _letpattern110: (&[u8], &[u8]) =
                            {
                                let input1: &[u8] = _letpattern19.0;
                                let input2: &[u8] = _letpattern19.1;
                                (input1,input2)
                            };
                        let _letpattern111: (&[u8], &[u8]) =
                            {
                                let input1: &[u8] = _letpattern110.0;
                                let input2: &[u8] = _letpattern110.1;
                                (input1,input2)
                            };
                        let _letpattern112: (&[u8], &[u8]) =
                            {
                                let left: &[u8] = _letpattern111.0;
                                let right: &[u8] = _letpattern111.1;
                                (left,right)
                            };
                        let lv: &[u8] = _letpattern112.0;
                        let lt·: &[u8] = _letpattern112.1;
                        let mut pll: [&[u8]; 1] = [c2; 1usize];
                        let mut pn1: [usize; 1] = [nv2; 1usize];
                        let mut pres1: [option__bool; 1] =
                            [option__bool::Some { v: false }; 1usize];
                        let mut pcont: [bool; 1] = [true; 1usize];
                        let n3: usize = (&pn1)[0];
                        let res0: option__bool = (&pres1)[0];
                        let cont: bool = (&pcont)[0];
                        let mut cond0: bool = n3 > 0usize && eq_Some_false(res0) && cont;
                        while
                        cond0
                        {
                            let l3: &[u8] = (&pll)[0];
                            let n30: usize = (&pn1)[0];
                            let n·1: usize = n30.wrapping_sub(1usize);
                            let i7: usize = jump_raw_data_item(l3, 0usize);
                            let s7: (&[u8], &[u8]) = l3.split_at(i7);
                            let _letpattern20: (&[u8], &[u8]) =
                                {
                                    let s10: &[u8] = s7.0;
                                    let s20: &[u8] = s7.1;
                                    (s10,s20)
                                };
                            let _letpattern21: (&[u8], &[u8]) =
                                {
                                    let input1: &[u8] = _letpattern20.0;
                                    let input2: &[u8] = _letpattern20.1;
                                    (input1,input2)
                                };
                            let _letpattern22: (&[u8], &[u8]) =
                                {
                                    let input1: &[u8] = _letpattern21.0;
                                    let input2: &[u8] = _letpattern21.1;
                                    (input1,input2)
                                };
                            let _letpattern23: (&[u8], &[u8]) =
                                {
                                    let left: &[u8] = _letpattern22.0;
                                    let right: &[u8] = _letpattern22.1;
                                    (left,right)
                                };
                            {
                                let lh1: &[u8] = _letpattern23.0;
                                let lt1: &[u8] = _letpattern23.1;
                                let mut pn2: [usize; 1] = [1usize; 1usize];
                                let mut pl1: [&[u8]; 1] = [lh; 1usize];
                                let mut pl2: [&[u8]; 1] = [lh1; 1usize];
                                let mut pres2: [option__bool; 1] =
                                    [option__bool::Some { v: true }; 1usize];
                                let res1: option__bool = (&pres2)[0];
                                let n4: usize = (&pn2)[0];
                                let mut cond1: bool = eq_Some_true(res1) && n4 > 0usize;
                                while
                                cond1
                                {
                                    let l1·: &[u8] = (&pl1)[0];
                                    let l2·: &[u8] = (&pl2)[0];
                                    let r: option__bool =
                                        impl_check_equiv_map_hd_basic(map_bound·, l1·, l2·);
                                    if uu___is_None__bool(r)
                                    { (&mut pres2)[0] = r }
                                    else
                                    {
                                        let n40: usize = (&pn2)[0];
                                        if eq_Some_true(r)
                                        {
                                            let n·2: usize = n40.wrapping_sub(1usize);
                                            let i8: usize = jump_raw_data_item(l1·, 0usize);
                                            let s8: (&[u8], &[u8]) = l1·.split_at(i8);
                                            let _letpattern30: (&[u8], &[u8]) =
                                                {
                                                    let s10: &[u8] = s8.0;
                                                    let s20: &[u8] = s8.1;
                                                    (s10,s20)
                                                };
                                            let _letpattern31: (&[u8], &[u8]) =
                                                {
                                                    let input1: &[u8] = _letpattern30.0;
                                                    let input2: &[u8] = _letpattern30.1;
                                                    (input1,input2)
                                                };
                                            let _letpattern32: (&[u8], &[u8]) =
                                                {
                                                    let input1: &[u8] = _letpattern31.0;
                                                    let input2: &[u8] = _letpattern31.1;
                                                    (input1,input2)
                                                };
                                            let tl1: &[u8] =
                                                {
                                                    let _input1: &[u8] = _letpattern32.0;
                                                    let input2: &[u8] = _letpattern32.1;
                                                    input2
                                                };
                                            let i9: usize = jump_raw_data_item(l2·, 0usize);
                                            let s9: (&[u8], &[u8]) = l2·.split_at(i9);
                                            let _letpattern33: (&[u8], &[u8]) =
                                                {
                                                    let s10: &[u8] = s9.0;
                                                    let s20: &[u8] = s9.1;
                                                    (s10,s20)
                                                };
                                            let _letpattern34: (&[u8], &[u8]) =
                                                {
                                                    let input1: &[u8] = _letpattern33.0;
                                                    let input2: &[u8] = _letpattern33.1;
                                                    (input1,input2)
                                                };
                                            let _letpattern35: (&[u8], &[u8]) =
                                                {
                                                    let input1: &[u8] = _letpattern34.0;
                                                    let input2: &[u8] = _letpattern34.1;
                                                    (input1,input2)
                                                };
                                            let tl2: &[u8] =
                                                {
                                                    let _input1: &[u8] = _letpattern35.0;
                                                    let input2: &[u8] = _letpattern35.1;
                                                    input2
                                                };
                                            (&mut pn2)[0] = n·2;
                                            (&mut pl1)[0] = tl1;
                                            (&mut pl2)[0] = tl2
                                        }
                                        else
                                        {
                                            let i8: usize = jump_header(l1·, 0usize);
                                            let s8: (&[u8], &[u8]) = l1·.split_at(i8);
                                            let _letpattern30: (&[u8], &[u8]) =
                                                {
                                                    let s10: &[u8] = s8.0;
                                                    let s20: &[u8] = s8.1;
                                                    (s10,s20)
                                                };
                                            let _letpattern31: (&[u8], &[u8]) =
                                                {
                                                    let input1: &[u8] = _letpattern30.0;
                                                    let input2: &[u8] = _letpattern30.1;
                                                    (input1,input2)
                                                };
                                            let _letpattern32: (&[u8], &[u8]) =
                                                {
                                                    let input1: &[u8] = _letpattern31.0;
                                                    let input2: &[u8] = _letpattern31.1;
                                                    (input1,input2)
                                                };
                                            let _letpattern33: (&[u8], &[u8]) =
                                                {
                                                    let left: &[u8] = _letpattern32.0;
                                                    let right: &[u8] = _letpattern32.1;
                                                    (left,right)
                                                };
                                            let hd1: &[u8] = _letpattern33.0;
                                            let tl1: &[u8] = _letpattern33.1;
                                            let h11: header = read_header(hd1);
                                            let mt11: u8 = get_header_major_type(h11);
                                            let i9: usize = jump_header(l2·, 0usize);
                                            let s9: (&[u8], &[u8]) = l2·.split_at(i9);
                                            let _letpattern40: (&[u8], &[u8]) =
                                                {
                                                    let s10: &[u8] = s9.0;
                                                    let s20: &[u8] = s9.1;
                                                    (s10,s20)
                                                };
                                            let _letpattern41: (&[u8], &[u8]) =
                                                {
                                                    let input1: &[u8] = _letpattern40.0;
                                                    let input2: &[u8] = _letpattern40.1;
                                                    (input1,input2)
                                                };
                                            let _letpattern42: (&[u8], &[u8]) =
                                                {
                                                    let input1: &[u8] = _letpattern41.0;
                                                    let input2: &[u8] = _letpattern41.1;
                                                    (input1,input2)
                                                };
                                            let _letpattern43: (&[u8], &[u8]) =
                                                {
                                                    let left: &[u8] = _letpattern42.0;
                                                    let right: &[u8] = _letpattern42.1;
                                                    (left,right)
                                                };
                                            let hd2: &[u8] = _letpattern43.0;
                                            let tl2: &[u8] = _letpattern43.1;
                                            let h21: header = read_header(hd2);
                                            let mt21: u8 = get_header_major_type(h21);
                                            if mt11 != mt21
                                            { (&mut pres2)[0] = option__bool::Some { v: false } }
                                            else
                                            {
                                                let b: initial_byte_t = h11.fst;
                                                let i10: usize =
                                                    if
                                                    b.major_type == cbor_major_type_byte_string
                                                    ||
                                                    b.major_type == cbor_major_type_text_string
                                                    {
                                                        let b0: initial_byte_t = h11.fst;
                                                        let l4: long_argument = h11.snd;
                                                        0usize.wrapping_add(
                                                            argument_as_uint64(b0, l4) as usize
                                                        )
                                                    }
                                                    else
                                                    { 0usize };
                                                let s10: (&[u8], &[u8]) = tl1.split_at(i10);
                                                let _letpattern50: (&[u8], &[u8]) =
                                                    {
                                                        let s11: &[u8] = s10.0;
                                                        let s20: &[u8] = s10.1;
                                                        (s11,s20)
                                                    };
                                                let _letpattern51: (&[u8], &[u8]) =
                                                    {
                                                        let input1: &[u8] = _letpattern50.0;
                                                        let input2: &[u8] = _letpattern50.1;
                                                        (input1,input2)
                                                    };
                                                let _letpattern52: (&[u8], &[u8]) =
                                                    {
                                                        let input1: &[u8] = _letpattern51.0;
                                                        let input2: &[u8] = _letpattern51.1;
                                                        (input1,input2)
                                                    };
                                                let _letpattern53: (&[u8], &[u8]) =
                                                    {
                                                        let left: &[u8] = _letpattern52.0;
                                                        let right: &[u8] = _letpattern52.1;
                                                        (left,right)
                                                    };
                                                let lc1: &[u8] = _letpattern53.0;
                                                let tl1·: &[u8] = _letpattern53.1;
                                                let n·2: usize =
                                                    (impl_remaining_data_items_header(h11)).wrapping_add(
                                                        n40.wrapping_sub(1usize)
                                                    );
                                                let b0: initial_byte_t = h21.fst;
                                                let i11: usize =
                                                    if
                                                    b0.major_type == cbor_major_type_byte_string
                                                    ||
                                                    b0.major_type == cbor_major_type_text_string
                                                    {
                                                        let b1: initial_byte_t = h21.fst;
                                                        let l4: long_argument = h21.snd;
                                                        0usize.wrapping_add(
                                                            argument_as_uint64(b1, l4) as usize
                                                        )
                                                    }
                                                    else
                                                    { 0usize };
                                                let s11: (&[u8], &[u8]) = tl2.split_at(i11);
                                                let _letpattern60: (&[u8], &[u8]) =
                                                    {
                                                        let s12: &[u8] = s11.0;
                                                        let s20: &[u8] = s11.1;
                                                        (s12,s20)
                                                    };
                                                let _letpattern61: (&[u8], &[u8]) =
                                                    {
                                                        let input1: &[u8] = _letpattern60.0;
                                                        let input2: &[u8] = _letpattern60.1;
                                                        (input1,input2)
                                                    };
                                                let _letpattern62: (&[u8], &[u8]) =
                                                    {
                                                        let input1: &[u8] = _letpattern61.0;
                                                        let input2: &[u8] = _letpattern61.1;
                                                        (input1,input2)
                                                    };
                                                let _letpattern63: (&[u8], &[u8]) =
                                                    {
                                                        let left: &[u8] = _letpattern62.0;
                                                        let right: &[u8] = _letpattern62.1;
                                                        (left,right)
                                                    };
                                                let lc2: &[u8] = _letpattern63.0;
                                                let tl2·: &[u8] = _letpattern63.1;
                                                let mt12: u8 = get_header_major_type(h11);
                                                let __anf01: bool =
                                                    if mt12 == cbor_major_type_simple_value
                                                    {
                                                        let sv1: u8 =
                                                            match
                                                            dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                h11
                                                            )
                                                            {
                                                                long_argument::LongArgumentOther =>
                                                                  (dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                      h11
                                                                  )).additional_info,
                                                                long_argument::LongArgumentSimpleValue
                                                                { v }
                                                                => v,
                                                                _ =>
                                                                  panic!(
                                                                      "Incomplete pattern matching"
                                                                  )
                                                            };
                                                        let sv2: u8 =
                                                            match
                                                            dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                h21
                                                            )
                                                            {
                                                                long_argument::LongArgumentOther =>
                                                                  (dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                      h21
                                                                  )).additional_info,
                                                                long_argument::LongArgumentSimpleValue
                                                                { v }
                                                                => v,
                                                                _ =>
                                                                  panic!(
                                                                      "Incomplete pattern matching"
                                                                  )
                                                            };
                                                        sv1 == sv2
                                                    }
                                                    else
                                                    {
                                                        let len: u64 =
                                                            argument_as_uint64(
                                                                dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                    h11
                                                                ),
                                                                dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                    h11
                                                                )
                                                            );
                                                        let len2: u64 =
                                                            argument_as_uint64(
                                                                dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                    h21
                                                                ),
                                                                dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                    h21
                                                                )
                                                            );
                                                        if len != len2
                                                        { false }
                                                        else if
                                                        mt12 == cbor_major_type_byte_string
                                                        ||
                                                        mt12 == cbor_major_type_text_string
                                                        {
                                                            let cmp: i16 =
                                                                lex_compare_bytes(lc1, lc2);
                                                            cmp == 0i16
                                                        }
                                                        else
                                                        { mt12 != cbor_major_type_map }
                                                    };
                                                if __anf01
                                                {
                                                    (&mut pn2)[0] = n·2;
                                                    (&mut pl1)[0] = tl1·;
                                                    (&mut pl2)[0] = tl2·
                                                }
                                                else
                                                {
                                                    (&mut pres2)[0] =
                                                        option__bool::Some { v: false }
                                                }
                                            }
                                        }
                                    };
                                    let res2: option__bool = (&pres2)[0];
                                    let n40: usize = (&pn2)[0];
                                    cond1 = eq_Some_true(res2) && n40 > 0usize
                                };
                                let res2: option__bool = (&pres2)[0];
                                if uu___is_None__bool(res2)
                                { (&mut pres1)[0] = res2 }
                                else
                                {
                                    let i8: usize = jump_raw_data_item(lt1, 0usize);
                                    let s8: (&[u8], &[u8]) = lt1.split_at(i8);
                                    let _letpattern30: (&[u8], &[u8]) =
                                        {
                                            let s10: &[u8] = s8.0;
                                            let s20: &[u8] = s8.1;
                                            (s10,s20)
                                        };
                                    let _letpattern31: (&[u8], &[u8]) =
                                        {
                                            let input1: &[u8] = _letpattern30.0;
                                            let input2: &[u8] = _letpattern30.1;
                                            (input1,input2)
                                        };
                                    let _letpattern32: (&[u8], &[u8]) =
                                        {
                                            let input1: &[u8] = _letpattern31.0;
                                            let input2: &[u8] = _letpattern31.1;
                                            (input1,input2)
                                        };
                                    let _letpattern33: (&[u8], &[u8]) =
                                        {
                                            let left: &[u8] = _letpattern32.0;
                                            let right: &[u8] = _letpattern32.1;
                                            (left,right)
                                        };
                                    let lv1: &[u8] = _letpattern33.0;
                                    let lt·1: &[u8] = _letpattern33.1;
                                    if
                                    match res2
                                    {
                                        option__bool::Some { v } => v,
                                        _ => panic!("Incomplete pattern matching")
                                    }
                                    {
                                        let mut pn20: [usize; 1] = [1usize; 1usize];
                                        let mut pl10: [&[u8]; 1] = [lv; 1usize];
                                        let mut pl20: [&[u8]; 1] = [lv1; 1usize];
                                        let mut pres20: [option__bool; 1] =
                                            [option__bool::Some { v: true }; 1usize];
                                        let res10: option__bool = (&pres20)[0];
                                        let n40: usize = (&pn20)[0];
                                        let mut cond2: bool = eq_Some_true(res10) && n40 > 0usize;
                                        while
                                        cond2
                                        {
                                            let l1·: &[u8] = (&pl10)[0];
                                            let l2·: &[u8] = (&pl20)[0];
                                            let r: option__bool =
                                                impl_check_equiv_map_hd_basic(
                                                    map_bound·,
                                                    l1·,
                                                    l2·
                                                );
                                            if uu___is_None__bool(r)
                                            { (&mut pres20)[0] = r }
                                            else
                                            {
                                                let n41: usize = (&pn20)[0];
                                                if eq_Some_true(r)
                                                {
                                                    let n·2: usize = n41.wrapping_sub(1usize);
                                                    let i9: usize =
                                                        jump_raw_data_item(l1·, 0usize);
                                                    let s9: (&[u8], &[u8]) = l1·.split_at(i9);
                                                    let _letpattern40: (&[u8], &[u8]) =
                                                        {
                                                            let s10: &[u8] = s9.0;
                                                            let s20: &[u8] = s9.1;
                                                            (s10,s20)
                                                        };
                                                    let _letpattern41: (&[u8], &[u8]) =
                                                        {
                                                            let input1: &[u8] = _letpattern40.0;
                                                            let input2: &[u8] = _letpattern40.1;
                                                            (input1,input2)
                                                        };
                                                    let _letpattern42: (&[u8], &[u8]) =
                                                        {
                                                            let input1: &[u8] = _letpattern41.0;
                                                            let input2: &[u8] = _letpattern41.1;
                                                            (input1,input2)
                                                        };
                                                    let tl1: &[u8] =
                                                        {
                                                            let _input1: &[u8] = _letpattern42.0;
                                                            let input2: &[u8] = _letpattern42.1;
                                                            input2
                                                        };
                                                    let i10: usize =
                                                        jump_raw_data_item(l2·, 0usize);
                                                    let s10: (&[u8], &[u8]) = l2·.split_at(i10);
                                                    let _letpattern43: (&[u8], &[u8]) =
                                                        {
                                                            let s11: &[u8] = s10.0;
                                                            let s20: &[u8] = s10.1;
                                                            (s11,s20)
                                                        };
                                                    let _letpattern44: (&[u8], &[u8]) =
                                                        {
                                                            let input1: &[u8] = _letpattern43.0;
                                                            let input2: &[u8] = _letpattern43.1;
                                                            (input1,input2)
                                                        };
                                                    let _letpattern45: (&[u8], &[u8]) =
                                                        {
                                                            let input1: &[u8] = _letpattern44.0;
                                                            let input2: &[u8] = _letpattern44.1;
                                                            (input1,input2)
                                                        };
                                                    let tl2: &[u8] =
                                                        {
                                                            let _input1: &[u8] = _letpattern45.0;
                                                            let input2: &[u8] = _letpattern45.1;
                                                            input2
                                                        };
                                                    (&mut pn20)[0] = n·2;
                                                    (&mut pl10)[0] = tl1;
                                                    (&mut pl20)[0] = tl2
                                                }
                                                else
                                                {
                                                    let i9: usize = jump_header(l1·, 0usize);
                                                    let s9: (&[u8], &[u8]) = l1·.split_at(i9);
                                                    let _letpattern40: (&[u8], &[u8]) =
                                                        {
                                                            let s10: &[u8] = s9.0;
                                                            let s20: &[u8] = s9.1;
                                                            (s10,s20)
                                                        };
                                                    let _letpattern41: (&[u8], &[u8]) =
                                                        {
                                                            let input1: &[u8] = _letpattern40.0;
                                                            let input2: &[u8] = _letpattern40.1;
                                                            (input1,input2)
                                                        };
                                                    let _letpattern42: (&[u8], &[u8]) =
                                                        {
                                                            let input1: &[u8] = _letpattern41.0;
                                                            let input2: &[u8] = _letpattern41.1;
                                                            (input1,input2)
                                                        };
                                                    let _letpattern43: (&[u8], &[u8]) =
                                                        {
                                                            let left: &[u8] = _letpattern42.0;
                                                            let right: &[u8] = _letpattern42.1;
                                                            (left,right)
                                                        };
                                                    let hd1: &[u8] = _letpattern43.0;
                                                    let tl1: &[u8] = _letpattern43.1;
                                                    let h11: header = read_header(hd1);
                                                    let mt11: u8 = get_header_major_type(h11);
                                                    let i10: usize = jump_header(l2·, 0usize);
                                                    let s10: (&[u8], &[u8]) = l2·.split_at(i10);
                                                    let _letpattern50: (&[u8], &[u8]) =
                                                        {
                                                            let s11: &[u8] = s10.0;
                                                            let s20: &[u8] = s10.1;
                                                            (s11,s20)
                                                        };
                                                    let _letpattern51: (&[u8], &[u8]) =
                                                        {
                                                            let input1: &[u8] = _letpattern50.0;
                                                            let input2: &[u8] = _letpattern50.1;
                                                            (input1,input2)
                                                        };
                                                    let _letpattern52: (&[u8], &[u8]) =
                                                        {
                                                            let input1: &[u8] = _letpattern51.0;
                                                            let input2: &[u8] = _letpattern51.1;
                                                            (input1,input2)
                                                        };
                                                    let _letpattern53: (&[u8], &[u8]) =
                                                        {
                                                            let left: &[u8] = _letpattern52.0;
                                                            let right: &[u8] = _letpattern52.1;
                                                            (left,right)
                                                        };
                                                    let hd2: &[u8] = _letpattern53.0;
                                                    let tl2: &[u8] = _letpattern53.1;
                                                    let h21: header = read_header(hd2);
                                                    let mt21: u8 = get_header_major_type(h21);
                                                    if mt11 != mt21
                                                    {
                                                        (&mut pres20)[0] =
                                                            option__bool::Some { v: false }
                                                    }
                                                    else
                                                    {
                                                        let b: initial_byte_t = h11.fst;
                                                        let i11: usize =
                                                            if
                                                            b.major_type
                                                            ==
                                                            cbor_major_type_byte_string
                                                            ||
                                                            b.major_type
                                                            ==
                                                            cbor_major_type_text_string
                                                            {
                                                                let b0: initial_byte_t = h11.fst;
                                                                let l4: long_argument = h11.snd;
                                                                0usize.wrapping_add(
                                                                    argument_as_uint64(b0, l4)
                                                                    as
                                                                    usize
                                                                )
                                                            }
                                                            else
                                                            { 0usize };
                                                        let s11: (&[u8], &[u8]) = tl1.split_at(i11);
                                                        let _letpattern60: (&[u8], &[u8]) =
                                                            {
                                                                let s12: &[u8] = s11.0;
                                                                let s20: &[u8] = s11.1;
                                                                (s12,s20)
                                                            };
                                                        let _letpattern61: (&[u8], &[u8]) =
                                                            {
                                                                let input1: &[u8] = _letpattern60.0;
                                                                let input2: &[u8] = _letpattern60.1;
                                                                (input1,input2)
                                                            };
                                                        let _letpattern62: (&[u8], &[u8]) =
                                                            {
                                                                let input1: &[u8] = _letpattern61.0;
                                                                let input2: &[u8] = _letpattern61.1;
                                                                (input1,input2)
                                                            };
                                                        let _letpattern63: (&[u8], &[u8]) =
                                                            {
                                                                let left: &[u8] = _letpattern62.0;
                                                                let right: &[u8] = _letpattern62.1;
                                                                (left,right)
                                                            };
                                                        let lc1: &[u8] = _letpattern63.0;
                                                        let tl1·: &[u8] = _letpattern63.1;
                                                        let n·2: usize =
                                                            (impl_remaining_data_items_header(h11)).wrapping_add(
                                                                n41.wrapping_sub(1usize)
                                                            );
                                                        let b0: initial_byte_t = h21.fst;
                                                        let i12: usize =
                                                            if
                                                            b0.major_type
                                                            ==
                                                            cbor_major_type_byte_string
                                                            ||
                                                            b0.major_type
                                                            ==
                                                            cbor_major_type_text_string
                                                            {
                                                                let b1: initial_byte_t = h21.fst;
                                                                let l4: long_argument = h21.snd;
                                                                0usize.wrapping_add(
                                                                    argument_as_uint64(b1, l4)
                                                                    as
                                                                    usize
                                                                )
                                                            }
                                                            else
                                                            { 0usize };
                                                        let s12: (&[u8], &[u8]) = tl2.split_at(i12);
                                                        let _letpattern70: (&[u8], &[u8]) =
                                                            {
                                                                let s13: &[u8] = s12.0;
                                                                let s20: &[u8] = s12.1;
                                                                (s13,s20)
                                                            };
                                                        let _letpattern71: (&[u8], &[u8]) =
                                                            {
                                                                let input1: &[u8] = _letpattern70.0;
                                                                let input2: &[u8] = _letpattern70.1;
                                                                (input1,input2)
                                                            };
                                                        let _letpattern72: (&[u8], &[u8]) =
                                                            {
                                                                let input1: &[u8] = _letpattern71.0;
                                                                let input2: &[u8] = _letpattern71.1;
                                                                (input1,input2)
                                                            };
                                                        let _letpattern73: (&[u8], &[u8]) =
                                                            {
                                                                let left: &[u8] = _letpattern72.0;
                                                                let right: &[u8] = _letpattern72.1;
                                                                (left,right)
                                                            };
                                                        let lc2: &[u8] = _letpattern73.0;
                                                        let tl2·: &[u8] = _letpattern73.1;
                                                        let mt12: u8 = get_header_major_type(h11);
                                                        let __anf01: bool =
                                                            if mt12 == cbor_major_type_simple_value
                                                            {
                                                                let sv1: u8 =
                                                                    match
                                                                    dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                        h11
                                                                    )
                                                                    {
                                                                        long_argument::LongArgumentOther
                                                                        =>
                                                                          (dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                              h11
                                                                          )).additional_info,
                                                                        long_argument::LongArgumentSimpleValue
                                                                        { v }
                                                                        => v,
                                                                        _ =>
                                                                          panic!(
                                                                              "Incomplete pattern matching"
                                                                          )
                                                                    };
                                                                let sv2: u8 =
                                                                    match
                                                                    dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                        h21
                                                                    )
                                                                    {
                                                                        long_argument::LongArgumentOther
                                                                        =>
                                                                          (dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                              h21
                                                                          )).additional_info,
                                                                        long_argument::LongArgumentSimpleValue
                                                                        { v }
                                                                        => v,
                                                                        _ =>
                                                                          panic!(
                                                                              "Incomplete pattern matching"
                                                                          )
                                                                    };
                                                                sv1 == sv2
                                                            }
                                                            else
                                                            {
                                                                let len: u64 =
                                                                    argument_as_uint64(
                                                                        dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                            h11
                                                                        ),
                                                                        dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                            h11
                                                                        )
                                                                    );
                                                                let len2: u64 =
                                                                    argument_as_uint64(
                                                                        dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                            h21
                                                                        ),
                                                                        dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                            h21
                                                                        )
                                                                    );
                                                                if len != len2
                                                                { false }
                                                                else if
                                                                mt12 == cbor_major_type_byte_string
                                                                ||
                                                                mt12 == cbor_major_type_text_string
                                                                {
                                                                    let cmp: i16 =
                                                                        lex_compare_bytes(lc1, lc2);
                                                                    cmp == 0i16
                                                                }
                                                                else
                                                                { mt12 != cbor_major_type_map }
                                                            };
                                                        if __anf01
                                                        {
                                                            (&mut pn20)[0] = n·2;
                                                            (&mut pl10)[0] = tl1·;
                                                            (&mut pl20)[0] = tl2·
                                                        }
                                                        else
                                                        {
                                                            (&mut pres20)[0] =
                                                                option__bool::Some { v: false }
                                                        }
                                                    }
                                                }
                                            };
                                            let res11: option__bool = (&pres20)[0];
                                            let n41: usize = (&pn20)[0];
                                            cond2 = eq_Some_true(res11) && n41 > 0usize
                                        };
                                        let __anf01: option__bool = (&pres20)[0];
                                        (&mut pres1)[0] = __anf01;
                                        (&mut pcont)[0] = false
                                    }
                                    else
                                    {
                                        (&mut pll)[0] = lt·1;
                                        (&mut pn1)[0] = n·1
                                    }
                                }
                            };
                            let n31: usize = (&pn1)[0];
                            let res1: option__bool = (&pres1)[0];
                            let cont0: bool = (&pcont)[0];
                            cond0 = n31 > 0usize && eq_Some_false(res1) && cont0
                        };
                        let res1: option__bool = (&pres1)[0];
                        if eq_Some_true(res1)
                        {
                            (&mut pl)[0] = lt·;
                            (&mut pn)[0] = n·
                        }
                        else
                        { (&mut pres)[0] = res1 }
                    };
                    let n1: usize = (&pn)[0];
                    let res0: option__bool = (&pres)[0];
                    cond = n1 > 0usize && eq_Some_true(res0)
                };
                let res0: option__bool = (&pres)[0];
                if eq_Some_true(res0)
                {
                    let mut pl0: [&[u8]; 1] = [c2; 1usize];
                    let mut pn0: [usize; 1] = [nv2; 1usize];
                    let mut pres0: [option__bool; 1] = [option__bool::Some { v: true }; 1usize];
                    let n0: usize = (&pn0)[0];
                    let res1: option__bool = (&pres0)[0];
                    let mut cond0: bool = n0 > 0usize && eq_Some_true(res1);
                    while
                    cond0
                    {
                        let l: &[u8] = (&pl0)[0];
                        let n1: usize = (&pn0)[0];
                        let n·: usize = n1.wrapping_sub(1usize);
                        let i5: usize = jump_raw_data_item(l, 0usize);
                        let s5: (&[u8], &[u8]) = l.split_at(i5);
                        let _letpattern15: (&[u8], &[u8]) =
                            {
                                let s10: &[u8] = s5.0;
                                let s20: &[u8] = s5.1;
                                (s10,s20)
                            };
                        let _letpattern16: (&[u8], &[u8]) =
                            {
                                let input1: &[u8] = _letpattern15.0;
                                let input2: &[u8] = _letpattern15.1;
                                (input1,input2)
                            };
                        let _letpattern17: (&[u8], &[u8]) =
                            {
                                let input1: &[u8] = _letpattern16.0;
                                let input2: &[u8] = _letpattern16.1;
                                (input1,input2)
                            };
                        let _letpattern18: (&[u8], &[u8]) =
                            {
                                let left: &[u8] = _letpattern17.0;
                                let right: &[u8] = _letpattern17.1;
                                (left,right)
                            };
                        {
                            let lh: &[u8] = _letpattern18.0;
                            let lt: &[u8] = _letpattern18.1;
                            let i6: usize = jump_raw_data_item(lt, 0usize);
                            let s6: (&[u8], &[u8]) = lt.split_at(i6);
                            let _letpattern19: (&[u8], &[u8]) =
                                {
                                    let s10: &[u8] = s6.0;
                                    let s20: &[u8] = s6.1;
                                    (s10,s20)
                                };
                            let _letpattern110: (&[u8], &[u8]) =
                                {
                                    let input1: &[u8] = _letpattern19.0;
                                    let input2: &[u8] = _letpattern19.1;
                                    (input1,input2)
                                };
                            let _letpattern111: (&[u8], &[u8]) =
                                {
                                    let input1: &[u8] = _letpattern110.0;
                                    let input2: &[u8] = _letpattern110.1;
                                    (input1,input2)
                                };
                            let _letpattern112: (&[u8], &[u8]) =
                                {
                                    let left: &[u8] = _letpattern111.0;
                                    let right: &[u8] = _letpattern111.1;
                                    (left,right)
                                };
                            let lv: &[u8] = _letpattern112.0;
                            let lt·: &[u8] = _letpattern112.1;
                            let mut pll: [&[u8]; 1] = [c1; 1usize];
                            let mut pn1: [usize; 1] = [nv1; 1usize];
                            let mut pres1: [option__bool; 1] =
                                [option__bool::Some { v: false }; 1usize];
                            let mut pcont: [bool; 1] = [true; 1usize];
                            let n3: usize = (&pn1)[0];
                            let res10: option__bool = (&pres1)[0];
                            let cont: bool = (&pcont)[0];
                            let mut cond1: bool = n3 > 0usize && eq_Some_false(res10) && cont;
                            while
                            cond1
                            {
                                let l3: &[u8] = (&pll)[0];
                                let n30: usize = (&pn1)[0];
                                let n·1: usize = n30.wrapping_sub(1usize);
                                let i7: usize = jump_raw_data_item(l3, 0usize);
                                let s7: (&[u8], &[u8]) = l3.split_at(i7);
                                let _letpattern20: (&[u8], &[u8]) =
                                    {
                                        let s10: &[u8] = s7.0;
                                        let s20: &[u8] = s7.1;
                                        (s10,s20)
                                    };
                                let _letpattern21: (&[u8], &[u8]) =
                                    {
                                        let input1: &[u8] = _letpattern20.0;
                                        let input2: &[u8] = _letpattern20.1;
                                        (input1,input2)
                                    };
                                let _letpattern22: (&[u8], &[u8]) =
                                    {
                                        let input1: &[u8] = _letpattern21.0;
                                        let input2: &[u8] = _letpattern21.1;
                                        (input1,input2)
                                    };
                                let _letpattern23: (&[u8], &[u8]) =
                                    {
                                        let left: &[u8] = _letpattern22.0;
                                        let right: &[u8] = _letpattern22.1;
                                        (left,right)
                                    };
                                {
                                    let lh1: &[u8] = _letpattern23.0;
                                    let lt1: &[u8] = _letpattern23.1;
                                    let mut pn2: [usize; 1] = [1usize; 1usize];
                                    let mut pl1: [&[u8]; 1] = [lh; 1usize];
                                    let mut pl2: [&[u8]; 1] = [lh1; 1usize];
                                    let mut pres2: [option__bool; 1] =
                                        [option__bool::Some { v: true }; 1usize];
                                    let res11: option__bool = (&pres2)[0];
                                    let n4: usize = (&pn2)[0];
                                    let mut cond2: bool = eq_Some_true(res11) && n4 > 0usize;
                                    while
                                    cond2
                                    {
                                        let l1·: &[u8] = (&pl1)[0];
                                        let l2·: &[u8] = (&pl2)[0];
                                        let r: option__bool =
                                            impl_check_equiv_map_hd_basic(map_bound·, l1·, l2·);
                                        if uu___is_None__bool(r)
                                        { (&mut pres2)[0] = r }
                                        else
                                        {
                                            let n40: usize = (&pn2)[0];
                                            if eq_Some_true(r)
                                            {
                                                let n·2: usize = n40.wrapping_sub(1usize);
                                                let i8: usize = jump_raw_data_item(l1·, 0usize);
                                                let s8: (&[u8], &[u8]) = l1·.split_at(i8);
                                                let _letpattern30: (&[u8], &[u8]) =
                                                    {
                                                        let s10: &[u8] = s8.0;
                                                        let s20: &[u8] = s8.1;
                                                        (s10,s20)
                                                    };
                                                let _letpattern31: (&[u8], &[u8]) =
                                                    {
                                                        let input1: &[u8] = _letpattern30.0;
                                                        let input2: &[u8] = _letpattern30.1;
                                                        (input1,input2)
                                                    };
                                                let _letpattern32: (&[u8], &[u8]) =
                                                    {
                                                        let input1: &[u8] = _letpattern31.0;
                                                        let input2: &[u8] = _letpattern31.1;
                                                        (input1,input2)
                                                    };
                                                let tl1: &[u8] =
                                                    {
                                                        let _input1: &[u8] = _letpattern32.0;
                                                        let input2: &[u8] = _letpattern32.1;
                                                        input2
                                                    };
                                                let i9: usize = jump_raw_data_item(l2·, 0usize);
                                                let s9: (&[u8], &[u8]) = l2·.split_at(i9);
                                                let _letpattern33: (&[u8], &[u8]) =
                                                    {
                                                        let s10: &[u8] = s9.0;
                                                        let s20: &[u8] = s9.1;
                                                        (s10,s20)
                                                    };
                                                let _letpattern34: (&[u8], &[u8]) =
                                                    {
                                                        let input1: &[u8] = _letpattern33.0;
                                                        let input2: &[u8] = _letpattern33.1;
                                                        (input1,input2)
                                                    };
                                                let _letpattern35: (&[u8], &[u8]) =
                                                    {
                                                        let input1: &[u8] = _letpattern34.0;
                                                        let input2: &[u8] = _letpattern34.1;
                                                        (input1,input2)
                                                    };
                                                let tl2: &[u8] =
                                                    {
                                                        let _input1: &[u8] = _letpattern35.0;
                                                        let input2: &[u8] = _letpattern35.1;
                                                        input2
                                                    };
                                                (&mut pn2)[0] = n·2;
                                                (&mut pl1)[0] = tl1;
                                                (&mut pl2)[0] = tl2
                                            }
                                            else
                                            {
                                                let i8: usize = jump_header(l1·, 0usize);
                                                let s8: (&[u8], &[u8]) = l1·.split_at(i8);
                                                let _letpattern30: (&[u8], &[u8]) =
                                                    {
                                                        let s10: &[u8] = s8.0;
                                                        let s20: &[u8] = s8.1;
                                                        (s10,s20)
                                                    };
                                                let _letpattern31: (&[u8], &[u8]) =
                                                    {
                                                        let input1: &[u8] = _letpattern30.0;
                                                        let input2: &[u8] = _letpattern30.1;
                                                        (input1,input2)
                                                    };
                                                let _letpattern32: (&[u8], &[u8]) =
                                                    {
                                                        let input1: &[u8] = _letpattern31.0;
                                                        let input2: &[u8] = _letpattern31.1;
                                                        (input1,input2)
                                                    };
                                                let _letpattern33: (&[u8], &[u8]) =
                                                    {
                                                        let left: &[u8] = _letpattern32.0;
                                                        let right: &[u8] = _letpattern32.1;
                                                        (left,right)
                                                    };
                                                let hd1: &[u8] = _letpattern33.0;
                                                let tl1: &[u8] = _letpattern33.1;
                                                let h11: header = read_header(hd1);
                                                let mt11: u8 = get_header_major_type(h11);
                                                let i9: usize = jump_header(l2·, 0usize);
                                                let s9: (&[u8], &[u8]) = l2·.split_at(i9);
                                                let _letpattern40: (&[u8], &[u8]) =
                                                    {
                                                        let s10: &[u8] = s9.0;
                                                        let s20: &[u8] = s9.1;
                                                        (s10,s20)
                                                    };
                                                let _letpattern41: (&[u8], &[u8]) =
                                                    {
                                                        let input1: &[u8] = _letpattern40.0;
                                                        let input2: &[u8] = _letpattern40.1;
                                                        (input1,input2)
                                                    };
                                                let _letpattern42: (&[u8], &[u8]) =
                                                    {
                                                        let input1: &[u8] = _letpattern41.0;
                                                        let input2: &[u8] = _letpattern41.1;
                                                        (input1,input2)
                                                    };
                                                let _letpattern43: (&[u8], &[u8]) =
                                                    {
                                                        let left: &[u8] = _letpattern42.0;
                                                        let right: &[u8] = _letpattern42.1;
                                                        (left,right)
                                                    };
                                                let hd2: &[u8] = _letpattern43.0;
                                                let tl2: &[u8] = _letpattern43.1;
                                                let h21: header = read_header(hd2);
                                                let mt21: u8 = get_header_major_type(h21);
                                                if mt11 != mt21
                                                {
                                                    (&mut pres2)[0] =
                                                        option__bool::Some { v: false }
                                                }
                                                else
                                                {
                                                    let b: initial_byte_t = h11.fst;
                                                    let i10: usize =
                                                        if
                                                        b.major_type == cbor_major_type_byte_string
                                                        ||
                                                        b.major_type == cbor_major_type_text_string
                                                        {
                                                            let b0: initial_byte_t = h11.fst;
                                                            let l4: long_argument = h11.snd;
                                                            0usize.wrapping_add(
                                                                argument_as_uint64(b0, l4) as usize
                                                            )
                                                        }
                                                        else
                                                        { 0usize };
                                                    let s10: (&[u8], &[u8]) = tl1.split_at(i10);
                                                    let _letpattern50: (&[u8], &[u8]) =
                                                        {
                                                            let s11: &[u8] = s10.0;
                                                            let s20: &[u8] = s10.1;
                                                            (s11,s20)
                                                        };
                                                    let _letpattern51: (&[u8], &[u8]) =
                                                        {
                                                            let input1: &[u8] = _letpattern50.0;
                                                            let input2: &[u8] = _letpattern50.1;
                                                            (input1,input2)
                                                        };
                                                    let _letpattern52: (&[u8], &[u8]) =
                                                        {
                                                            let input1: &[u8] = _letpattern51.0;
                                                            let input2: &[u8] = _letpattern51.1;
                                                            (input1,input2)
                                                        };
                                                    let _letpattern53: (&[u8], &[u8]) =
                                                        {
                                                            let left: &[u8] = _letpattern52.0;
                                                            let right: &[u8] = _letpattern52.1;
                                                            (left,right)
                                                        };
                                                    let lc1: &[u8] = _letpattern53.0;
                                                    let tl1·: &[u8] = _letpattern53.1;
                                                    let n·2: usize =
                                                        (impl_remaining_data_items_header(h11)).wrapping_add(
                                                            n40.wrapping_sub(1usize)
                                                        );
                                                    let b0: initial_byte_t = h21.fst;
                                                    let i11: usize =
                                                        if
                                                        b0.major_type == cbor_major_type_byte_string
                                                        ||
                                                        b0.major_type == cbor_major_type_text_string
                                                        {
                                                            let b1: initial_byte_t = h21.fst;
                                                            let l4: long_argument = h21.snd;
                                                            0usize.wrapping_add(
                                                                argument_as_uint64(b1, l4) as usize
                                                            )
                                                        }
                                                        else
                                                        { 0usize };
                                                    let s11: (&[u8], &[u8]) = tl2.split_at(i11);
                                                    let _letpattern60: (&[u8], &[u8]) =
                                                        {
                                                            let s12: &[u8] = s11.0;
                                                            let s20: &[u8] = s11.1;
                                                            (s12,s20)
                                                        };
                                                    let _letpattern61: (&[u8], &[u8]) =
                                                        {
                                                            let input1: &[u8] = _letpattern60.0;
                                                            let input2: &[u8] = _letpattern60.1;
                                                            (input1,input2)
                                                        };
                                                    let _letpattern62: (&[u8], &[u8]) =
                                                        {
                                                            let input1: &[u8] = _letpattern61.0;
                                                            let input2: &[u8] = _letpattern61.1;
                                                            (input1,input2)
                                                        };
                                                    let _letpattern63: (&[u8], &[u8]) =
                                                        {
                                                            let left: &[u8] = _letpattern62.0;
                                                            let right: &[u8] = _letpattern62.1;
                                                            (left,right)
                                                        };
                                                    let lc2: &[u8] = _letpattern63.0;
                                                    let tl2·: &[u8] = _letpattern63.1;
                                                    let mt12: u8 = get_header_major_type(h11);
                                                    let __anf01: bool =
                                                        if mt12 == cbor_major_type_simple_value
                                                        {
                                                            let sv1: u8 =
                                                                match
                                                                dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                    h11
                                                                )
                                                                {
                                                                    long_argument::LongArgumentOther
                                                                    =>
                                                                      (dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                          h11
                                                                      )).additional_info,
                                                                    long_argument::LongArgumentSimpleValue
                                                                    { v }
                                                                    => v,
                                                                    _ =>
                                                                      panic!(
                                                                          "Incomplete pattern matching"
                                                                      )
                                                                };
                                                            let sv2: u8 =
                                                                match
                                                                dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                    h21
                                                                )
                                                                {
                                                                    long_argument::LongArgumentOther
                                                                    =>
                                                                      (dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                          h21
                                                                      )).additional_info,
                                                                    long_argument::LongArgumentSimpleValue
                                                                    { v }
                                                                    => v,
                                                                    _ =>
                                                                      panic!(
                                                                          "Incomplete pattern matching"
                                                                      )
                                                                };
                                                            sv1 == sv2
                                                        }
                                                        else
                                                        {
                                                            let len: u64 =
                                                                argument_as_uint64(
                                                                    dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                        h11
                                                                    ),
                                                                    dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                        h11
                                                                    )
                                                                );
                                                            let len2: u64 =
                                                                argument_as_uint64(
                                                                    dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                        h21
                                                                    ),
                                                                    dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                        h21
                                                                    )
                                                                );
                                                            if len != len2
                                                            { false }
                                                            else if
                                                            mt12 == cbor_major_type_byte_string
                                                            ||
                                                            mt12 == cbor_major_type_text_string
                                                            {
                                                                let cmp: i16 =
                                                                    lex_compare_bytes(lc1, lc2);
                                                                cmp == 0i16
                                                            }
                                                            else
                                                            { mt12 != cbor_major_type_map }
                                                        };
                                                    if __anf01
                                                    {
                                                        (&mut pn2)[0] = n·2;
                                                        (&mut pl1)[0] = tl1·;
                                                        (&mut pl2)[0] = tl2·
                                                    }
                                                    else
                                                    {
                                                        (&mut pres2)[0] =
                                                            option__bool::Some { v: false }
                                                    }
                                                }
                                            }
                                        };
                                        let res12: option__bool = (&pres2)[0];
                                        let n40: usize = (&pn2)[0];
                                        cond2 = eq_Some_true(res12) && n40 > 0usize
                                    };
                                    let res12: option__bool = (&pres2)[0];
                                    if uu___is_None__bool(res12)
                                    { (&mut pres1)[0] = res12 }
                                    else
                                    {
                                        let i8: usize = jump_raw_data_item(lt1, 0usize);
                                        let s8: (&[u8], &[u8]) = lt1.split_at(i8);
                                        let _letpattern30: (&[u8], &[u8]) =
                                            {
                                                let s10: &[u8] = s8.0;
                                                let s20: &[u8] = s8.1;
                                                (s10,s20)
                                            };
                                        let _letpattern31: (&[u8], &[u8]) =
                                            {
                                                let input1: &[u8] = _letpattern30.0;
                                                let input2: &[u8] = _letpattern30.1;
                                                (input1,input2)
                                            };
                                        let _letpattern32: (&[u8], &[u8]) =
                                            {
                                                let input1: &[u8] = _letpattern31.0;
                                                let input2: &[u8] = _letpattern31.1;
                                                (input1,input2)
                                            };
                                        let _letpattern33: (&[u8], &[u8]) =
                                            {
                                                let left: &[u8] = _letpattern32.0;
                                                let right: &[u8] = _letpattern32.1;
                                                (left,right)
                                            };
                                        let lv1: &[u8] = _letpattern33.0;
                                        let lt·1: &[u8] = _letpattern33.1;
                                        if
                                        match res12
                                        {
                                            option__bool::Some { v } => v,
                                            _ => panic!("Incomplete pattern matching")
                                        }
                                        {
                                            let mut pn20: [usize; 1] = [1usize; 1usize];
                                            let mut pl10: [&[u8]; 1] = [lv; 1usize];
                                            let mut pl20: [&[u8]; 1] = [lv1; 1usize];
                                            let mut pres20: [option__bool; 1] =
                                                [option__bool::Some { v: true }; 1usize];
                                            let res2: option__bool = (&pres20)[0];
                                            let n40: usize = (&pn20)[0];
                                            let mut cond3: bool =
                                                eq_Some_true(res2) && n40 > 0usize;
                                            while
                                            cond3
                                            {
                                                let l1·: &[u8] = (&pl10)[0];
                                                let l2·: &[u8] = (&pl20)[0];
                                                let r: option__bool =
                                                    impl_check_equiv_map_hd_basic(
                                                        map_bound·,
                                                        l1·,
                                                        l2·
                                                    );
                                                if uu___is_None__bool(r)
                                                { (&mut pres20)[0] = r }
                                                else
                                                {
                                                    let n41: usize = (&pn20)[0];
                                                    if eq_Some_true(r)
                                                    {
                                                        let n·2: usize = n41.wrapping_sub(1usize);
                                                        let i9: usize =
                                                            jump_raw_data_item(l1·, 0usize);
                                                        let s9: (&[u8], &[u8]) = l1·.split_at(i9);
                                                        let _letpattern40: (&[u8], &[u8]) =
                                                            {
                                                                let s10: &[u8] = s9.0;
                                                                let s20: &[u8] = s9.1;
                                                                (s10,s20)
                                                            };
                                                        let _letpattern41: (&[u8], &[u8]) =
                                                            {
                                                                let input1: &[u8] = _letpattern40.0;
                                                                let input2: &[u8] = _letpattern40.1;
                                                                (input1,input2)
                                                            };
                                                        let _letpattern42: (&[u8], &[u8]) =
                                                            {
                                                                let input1: &[u8] = _letpattern41.0;
                                                                let input2: &[u8] = _letpattern41.1;
                                                                (input1,input2)
                                                            };
                                                        let tl1: &[u8] =
                                                            {
                                                                let _input1: &[u8] =
                                                                    _letpattern42.0;
                                                                let input2: &[u8] = _letpattern42.1;
                                                                input2
                                                            };
                                                        let i10: usize =
                                                            jump_raw_data_item(l2·, 0usize);
                                                        let s10: (&[u8], &[u8]) =
                                                            l2·.split_at(i10);
                                                        let _letpattern43: (&[u8], &[u8]) =
                                                            {
                                                                let s11: &[u8] = s10.0;
                                                                let s20: &[u8] = s10.1;
                                                                (s11,s20)
                                                            };
                                                        let _letpattern44: (&[u8], &[u8]) =
                                                            {
                                                                let input1: &[u8] = _letpattern43.0;
                                                                let input2: &[u8] = _letpattern43.1;
                                                                (input1,input2)
                                                            };
                                                        let _letpattern45: (&[u8], &[u8]) =
                                                            {
                                                                let input1: &[u8] = _letpattern44.0;
                                                                let input2: &[u8] = _letpattern44.1;
                                                                (input1,input2)
                                                            };
                                                        let tl2: &[u8] =
                                                            {
                                                                let _input1: &[u8] =
                                                                    _letpattern45.0;
                                                                let input2: &[u8] = _letpattern45.1;
                                                                input2
                                                            };
                                                        (&mut pn20)[0] = n·2;
                                                        (&mut pl10)[0] = tl1;
                                                        (&mut pl20)[0] = tl2
                                                    }
                                                    else
                                                    {
                                                        let i9: usize = jump_header(l1·, 0usize);
                                                        let s9: (&[u8], &[u8]) = l1·.split_at(i9);
                                                        let _letpattern40: (&[u8], &[u8]) =
                                                            {
                                                                let s10: &[u8] = s9.0;
                                                                let s20: &[u8] = s9.1;
                                                                (s10,s20)
                                                            };
                                                        let _letpattern41: (&[u8], &[u8]) =
                                                            {
                                                                let input1: &[u8] = _letpattern40.0;
                                                                let input2: &[u8] = _letpattern40.1;
                                                                (input1,input2)
                                                            };
                                                        let _letpattern42: (&[u8], &[u8]) =
                                                            {
                                                                let input1: &[u8] = _letpattern41.0;
                                                                let input2: &[u8] = _letpattern41.1;
                                                                (input1,input2)
                                                            };
                                                        let _letpattern43: (&[u8], &[u8]) =
                                                            {
                                                                let left: &[u8] = _letpattern42.0;
                                                                let right: &[u8] = _letpattern42.1;
                                                                (left,right)
                                                            };
                                                        let hd1: &[u8] = _letpattern43.0;
                                                        let tl1: &[u8] = _letpattern43.1;
                                                        let h11: header = read_header(hd1);
                                                        let mt11: u8 = get_header_major_type(h11);
                                                        let i10: usize = jump_header(l2·, 0usize);
                                                        let s10: (&[u8], &[u8]) =
                                                            l2·.split_at(i10);
                                                        let _letpattern50: (&[u8], &[u8]) =
                                                            {
                                                                let s11: &[u8] = s10.0;
                                                                let s20: &[u8] = s10.1;
                                                                (s11,s20)
                                                            };
                                                        let _letpattern51: (&[u8], &[u8]) =
                                                            {
                                                                let input1: &[u8] = _letpattern50.0;
                                                                let input2: &[u8] = _letpattern50.1;
                                                                (input1,input2)
                                                            };
                                                        let _letpattern52: (&[u8], &[u8]) =
                                                            {
                                                                let input1: &[u8] = _letpattern51.0;
                                                                let input2: &[u8] = _letpattern51.1;
                                                                (input1,input2)
                                                            };
                                                        let _letpattern53: (&[u8], &[u8]) =
                                                            {
                                                                let left: &[u8] = _letpattern52.0;
                                                                let right: &[u8] = _letpattern52.1;
                                                                (left,right)
                                                            };
                                                        let hd2: &[u8] = _letpattern53.0;
                                                        let tl2: &[u8] = _letpattern53.1;
                                                        let h21: header = read_header(hd2);
                                                        let mt21: u8 = get_header_major_type(h21);
                                                        if mt11 != mt21
                                                        {
                                                            (&mut pres20)[0] =
                                                                option__bool::Some { v: false }
                                                        }
                                                        else
                                                        {
                                                            let b: initial_byte_t = h11.fst;
                                                            let i11: usize =
                                                                if
                                                                b.major_type
                                                                ==
                                                                cbor_major_type_byte_string
                                                                ||
                                                                b.major_type
                                                                ==
                                                                cbor_major_type_text_string
                                                                {
                                                                    let b0: initial_byte_t =
                                                                        h11.fst;
                                                                    let l4: long_argument = h11.snd;
                                                                    0usize.wrapping_add(
                                                                        argument_as_uint64(b0, l4)
                                                                        as
                                                                        usize
                                                                    )
                                                                }
                                                                else
                                                                { 0usize };
                                                            let s11: (&[u8], &[u8]) =
                                                                tl1.split_at(i11);
                                                            let _letpattern60: (&[u8], &[u8]) =
                                                                {
                                                                    let s12: &[u8] = s11.0;
                                                                    let s20: &[u8] = s11.1;
                                                                    (s12,s20)
                                                                };
                                                            let _letpattern61: (&[u8], &[u8]) =
                                                                {
                                                                    let input1: &[u8] =
                                                                        _letpattern60.0;
                                                                    let input2: &[u8] =
                                                                        _letpattern60.1;
                                                                    (input1,input2)
                                                                };
                                                            let _letpattern62: (&[u8], &[u8]) =
                                                                {
                                                                    let input1: &[u8] =
                                                                        _letpattern61.0;
                                                                    let input2: &[u8] =
                                                                        _letpattern61.1;
                                                                    (input1,input2)
                                                                };
                                                            let _letpattern63: (&[u8], &[u8]) =
                                                                {
                                                                    let left: &[u8] =
                                                                        _letpattern62.0;
                                                                    let right: &[u8] =
                                                                        _letpattern62.1;
                                                                    (left,right)
                                                                };
                                                            let lc1: &[u8] = _letpattern63.0;
                                                            let tl1·: &[u8] = _letpattern63.1;
                                                            let n·2: usize =
                                                                (impl_remaining_data_items_header(
                                                                    h11
                                                                )).wrapping_add(
                                                                    n41.wrapping_sub(1usize)
                                                                );
                                                            let b0: initial_byte_t = h21.fst;
                                                            let i12: usize =
                                                                if
                                                                b0.major_type
                                                                ==
                                                                cbor_major_type_byte_string
                                                                ||
                                                                b0.major_type
                                                                ==
                                                                cbor_major_type_text_string
                                                                {
                                                                    let b1: initial_byte_t =
                                                                        h21.fst;
                                                                    let l4: long_argument = h21.snd;
                                                                    0usize.wrapping_add(
                                                                        argument_as_uint64(b1, l4)
                                                                        as
                                                                        usize
                                                                    )
                                                                }
                                                                else
                                                                { 0usize };
                                                            let s12: (&[u8], &[u8]) =
                                                                tl2.split_at(i12);
                                                            let _letpattern70: (&[u8], &[u8]) =
                                                                {
                                                                    let s13: &[u8] = s12.0;
                                                                    let s20: &[u8] = s12.1;
                                                                    (s13,s20)
                                                                };
                                                            let _letpattern71: (&[u8], &[u8]) =
                                                                {
                                                                    let input1: &[u8] =
                                                                        _letpattern70.0;
                                                                    let input2: &[u8] =
                                                                        _letpattern70.1;
                                                                    (input1,input2)
                                                                };
                                                            let _letpattern72: (&[u8], &[u8]) =
                                                                {
                                                                    let input1: &[u8] =
                                                                        _letpattern71.0;
                                                                    let input2: &[u8] =
                                                                        _letpattern71.1;
                                                                    (input1,input2)
                                                                };
                                                            let _letpattern73: (&[u8], &[u8]) =
                                                                {
                                                                    let left: &[u8] =
                                                                        _letpattern72.0;
                                                                    let right: &[u8] =
                                                                        _letpattern72.1;
                                                                    (left,right)
                                                                };
                                                            let lc2: &[u8] = _letpattern73.0;
                                                            let tl2·: &[u8] = _letpattern73.1;
                                                            let mt12: u8 =
                                                                get_header_major_type(h11);
                                                            let __anf01: bool =
                                                                if
                                                                mt12 == cbor_major_type_simple_value
                                                                {
                                                                    let sv1: u8 =
                                                                        match
                                                                        dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                            h11
                                                                        )
                                                                        {
                                                                            long_argument::LongArgumentOther
                                                                            =>
                                                                              (dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                                  h11
                                                                              )).additional_info,
                                                                            long_argument::LongArgumentSimpleValue
                                                                            { v }
                                                                            => v,
                                                                            _ =>
                                                                              panic!(
                                                                                  "Incomplete pattern matching"
                                                                              )
                                                                        };
                                                                    let sv2: u8 =
                                                                        match
                                                                        dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                            h21
                                                                        )
                                                                        {
                                                                            long_argument::LongArgumentOther
                                                                            =>
                                                                              (dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                                  h21
                                                                              )).additional_info,
                                                                            long_argument::LongArgumentSimpleValue
                                                                            { v }
                                                                            => v,
                                                                            _ =>
                                                                              panic!(
                                                                                  "Incomplete pattern matching"
                                                                              )
                                                                        };
                                                                    sv1 == sv2
                                                                }
                                                                else
                                                                {
                                                                    let len: u64 =
                                                                        argument_as_uint64(
                                                                            dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                                h11
                                                                            ),
                                                                            dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                                h11
                                                                            )
                                                                        );
                                                                    let len2: u64 =
                                                                        argument_as_uint64(
                                                                            dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                                h21
                                                                            ),
                                                                            dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                                                                h21
                                                                            )
                                                                        );
                                                                    if len != len2
                                                                    { false }
                                                                    else if
                                                                    mt12
                                                                    ==
                                                                    cbor_major_type_byte_string
                                                                    ||
                                                                    mt12
                                                                    ==
                                                                    cbor_major_type_text_string
                                                                    {
                                                                        let cmp: i16 =
                                                                            lex_compare_bytes(
                                                                                lc1,
                                                                                lc2
                                                                            );
                                                                        cmp == 0i16
                                                                    }
                                                                    else
                                                                    { mt12 != cbor_major_type_map }
                                                                };
                                                            if __anf01
                                                            {
                                                                (&mut pn20)[0] = n·2;
                                                                (&mut pl10)[0] = tl1·;
                                                                (&mut pl20)[0] = tl2·
                                                            }
                                                            else
                                                            {
                                                                (&mut pres20)[0] =
                                                                    option__bool::Some { v: false }
                                                            }
                                                        }
                                                    }
                                                };
                                                let res20: option__bool = (&pres20)[0];
                                                let n41: usize = (&pn20)[0];
                                                cond3 = eq_Some_true(res20) && n41 > 0usize
                                            };
                                            let __anf01: option__bool = (&pres20)[0];
                                            (&mut pres1)[0] = __anf01;
                                            (&mut pcont)[0] = false
                                        }
                                        else
                                        {
                                            (&mut pll)[0] = lt·1;
                                            (&mut pn1)[0] = n·1
                                        }
                                    }
                                };
                                let n31: usize = (&pn1)[0];
                                let res11: option__bool = (&pres1)[0];
                                let cont0: bool = (&pcont)[0];
                                cond1 = n31 > 0usize && eq_Some_false(res11) && cont0
                            };
                            let res11: option__bool = (&pres1)[0];
                            if eq_Some_true(res11)
                            {
                                (&mut pl0)[0] = lt·;
                                (&mut pn0)[0] = n·
                            }
                            else
                            { (&mut pres0)[0] = res11 }
                        };
                        let n2: usize = (&pn0)[0];
                        let res10: option__bool = (&pres0)[0];
                        cond0 = n2 > 0usize && eq_Some_true(res10)
                    };
                    (&pres0)[0]
                }
                else
                { res0 }
            }
        }
        else
        { option__bool::Some { v: false } }
    }
}

fn impl_check_equiv_list_basic(
    map_bound: option__size_t,
    n1: usize,
    l1: &[u8],
    n2: usize,
    l2: &[u8]
) ->
    option__bool
{
    if n1 != n2
    { option__bool::Some { v: false } }
    else
    {
        let mut pn: [usize; 1] = [n1; 1usize];
        let mut pl1: [&[u8]; 1] = [l1; 1usize];
        let mut pl2: [&[u8]; 1] = [l2; 1usize];
        let mut pres: [option__bool; 1] = [option__bool::Some { v: true }; 1usize];
        let res: option__bool = (&pres)[0];
        let n: usize = (&pn)[0];
        let mut cond: bool = eq_Some_true(res) && n > 0usize;
        while
        cond
        {
            let l1·: &[u8] = (&pl1)[0];
            let l2·: &[u8] = (&pl2)[0];
            let r: option__bool = impl_check_equiv_map_hd_basic(map_bound, l1·, l2·);
            if uu___is_None__bool(r)
            { (&mut pres)[0] = r }
            else
            {
                let n0: usize = (&pn)[0];
                if eq_Some_true(r)
                {
                    let n·: usize = n0.wrapping_sub(1usize);
                    let i: usize = jump_raw_data_item(l1·, 0usize);
                    let s: (&[u8], &[u8]) = l1·.split_at(i);
                    let _letpattern: (&[u8], &[u8]) =
                        {
                            let s1: &[u8] = s.0;
                            let s2: &[u8] = s.1;
                            (s1,s2)
                        };
                    let _letpattern0: (&[u8], &[u8]) =
                        {
                            let input1: &[u8] = _letpattern.0;
                            let input2: &[u8] = _letpattern.1;
                            (input1,input2)
                        };
                    let _letpattern1: (&[u8], &[u8]) =
                        {
                            let input1: &[u8] = _letpattern0.0;
                            let input2: &[u8] = _letpattern0.1;
                            (input1,input2)
                        };
                    let tl1: &[u8] =
                        {
                            let _input1: &[u8] = _letpattern1.0;
                            let input2: &[u8] = _letpattern1.1;
                            input2
                        };
                    let i0: usize = jump_raw_data_item(l2·, 0usize);
                    let s0: (&[u8], &[u8]) = l2·.split_at(i0);
                    let _letpattern2: (&[u8], &[u8]) =
                        {
                            let s1: &[u8] = s0.0;
                            let s2: &[u8] = s0.1;
                            (s1,s2)
                        };
                    let _letpattern3: (&[u8], &[u8]) =
                        {
                            let input1: &[u8] = _letpattern2.0;
                            let input2: &[u8] = _letpattern2.1;
                            (input1,input2)
                        };
                    let _letpattern4: (&[u8], &[u8]) =
                        {
                            let input1: &[u8] = _letpattern3.0;
                            let input2: &[u8] = _letpattern3.1;
                            (input1,input2)
                        };
                    let tl2: &[u8] =
                        {
                            let _input1: &[u8] = _letpattern4.0;
                            let input2: &[u8] = _letpattern4.1;
                            input2
                        };
                    (&mut pn)[0] = n·;
                    (&mut pl1)[0] = tl1;
                    (&mut pl2)[0] = tl2
                }
                else
                {
                    let i: usize = jump_header(l1·, 0usize);
                    let s: (&[u8], &[u8]) = l1·.split_at(i);
                    let _letpattern: (&[u8], &[u8]) =
                        {
                            let s1: &[u8] = s.0;
                            let s2: &[u8] = s.1;
                            (s1,s2)
                        };
                    let _letpattern0: (&[u8], &[u8]) =
                        {
                            let input1: &[u8] = _letpattern.0;
                            let input2: &[u8] = _letpattern.1;
                            (input1,input2)
                        };
                    let _letpattern1: (&[u8], &[u8]) =
                        {
                            let input1: &[u8] = _letpattern0.0;
                            let input2: &[u8] = _letpattern0.1;
                            (input1,input2)
                        };
                    let _letpattern2: (&[u8], &[u8]) =
                        {
                            let left: &[u8] = _letpattern1.0;
                            let right: &[u8] = _letpattern1.1;
                            (left,right)
                        };
                    let hd1: &[u8] = _letpattern2.0;
                    let tl1: &[u8] = _letpattern2.1;
                    let h1: header = read_header(hd1);
                    let mt1: u8 = get_header_major_type(h1);
                    let i0: usize = jump_header(l2·, 0usize);
                    let s0: (&[u8], &[u8]) = l2·.split_at(i0);
                    let _letpattern10: (&[u8], &[u8]) =
                        {
                            let s1: &[u8] = s0.0;
                            let s2: &[u8] = s0.1;
                            (s1,s2)
                        };
                    let _letpattern11: (&[u8], &[u8]) =
                        {
                            let input1: &[u8] = _letpattern10.0;
                            let input2: &[u8] = _letpattern10.1;
                            (input1,input2)
                        };
                    let _letpattern12: (&[u8], &[u8]) =
                        {
                            let input1: &[u8] = _letpattern11.0;
                            let input2: &[u8] = _letpattern11.1;
                            (input1,input2)
                        };
                    let _letpattern13: (&[u8], &[u8]) =
                        {
                            let left: &[u8] = _letpattern12.0;
                            let right: &[u8] = _letpattern12.1;
                            (left,right)
                        };
                    let hd2: &[u8] = _letpattern13.0;
                    let tl2: &[u8] = _letpattern13.1;
                    let h2: header = read_header(hd2);
                    let mt2: u8 = get_header_major_type(h2);
                    if mt1 != mt2
                    { (&mut pres)[0] = option__bool::Some { v: false } }
                    else
                    {
                        let b: initial_byte_t = h1.fst;
                        let i1: usize =
                            if
                            b.major_type == cbor_major_type_byte_string
                            ||
                            b.major_type == cbor_major_type_text_string
                            {
                                let b0: initial_byte_t = h1.fst;
                                let l: long_argument = h1.snd;
                                0usize.wrapping_add(argument_as_uint64(b0, l) as usize)
                            }
                            else
                            { 0usize };
                        let s1: (&[u8], &[u8]) = tl1.split_at(i1);
                        let _letpattern20: (&[u8], &[u8]) =
                            {
                                let s10: &[u8] = s1.0;
                                let s2: &[u8] = s1.1;
                                (s10,s2)
                            };
                        let _letpattern21: (&[u8], &[u8]) =
                            {
                                let input1: &[u8] = _letpattern20.0;
                                let input2: &[u8] = _letpattern20.1;
                                (input1,input2)
                            };
                        let _letpattern22: (&[u8], &[u8]) =
                            {
                                let input1: &[u8] = _letpattern21.0;
                                let input2: &[u8] = _letpattern21.1;
                                (input1,input2)
                            };
                        let _letpattern23: (&[u8], &[u8]) =
                            {
                                let left: &[u8] = _letpattern22.0;
                                let right: &[u8] = _letpattern22.1;
                                (left,right)
                            };
                        let lc1: &[u8] = _letpattern23.0;
                        let tl1·: &[u8] = _letpattern23.1;
                        let n·: usize =
                            (impl_remaining_data_items_header(h1)).wrapping_add(
                                n0.wrapping_sub(1usize)
                            );
                        let b0: initial_byte_t = h2.fst;
                        let i2: usize =
                            if
                            b0.major_type == cbor_major_type_byte_string
                            ||
                            b0.major_type == cbor_major_type_text_string
                            {
                                let b1: initial_byte_t = h2.fst;
                                let l: long_argument = h2.snd;
                                0usize.wrapping_add(argument_as_uint64(b1, l) as usize)
                            }
                            else
                            { 0usize };
                        let s2: (&[u8], &[u8]) = tl2.split_at(i2);
                        let _letpattern3: (&[u8], &[u8]) =
                            {
                                let s10: &[u8] = s2.0;
                                let s20: &[u8] = s2.1;
                                (s10,s20)
                            };
                        let _letpattern30: (&[u8], &[u8]) =
                            {
                                let input1: &[u8] = _letpattern3.0;
                                let input2: &[u8] = _letpattern3.1;
                                (input1,input2)
                            };
                        let _letpattern31: (&[u8], &[u8]) =
                            {
                                let input1: &[u8] = _letpattern30.0;
                                let input2: &[u8] = _letpattern30.1;
                                (input1,input2)
                            };
                        let _letpattern32: (&[u8], &[u8]) =
                            {
                                let left: &[u8] = _letpattern31.0;
                                let right: &[u8] = _letpattern31.1;
                                (left,right)
                            };
                        let lc2: &[u8] = _letpattern32.0;
                        let tl2·: &[u8] = _letpattern32.1;
                        let mt11: u8 = get_header_major_type(h1);
                        let __anf0: bool =
                            if mt11 == cbor_major_type_simple_value
                            {
                                let sv1: u8 =
                                    match
                                    dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                        h1
                                    )
                                    {
                                        long_argument::LongArgumentOther =>
                                          (dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                              h1
                                          )).additional_info,
                                        long_argument::LongArgumentSimpleValue { v } => v,
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                let sv2: u8 =
                                    match
                                    dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                        h2
                                    )
                                    {
                                        long_argument::LongArgumentOther =>
                                          (dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                              h2
                                          )).additional_info,
                                        long_argument::LongArgumentSimpleValue { v } => v,
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                sv1 == sv2
                            }
                            else
                            {
                                let len: u64 =
                                    argument_as_uint64(
                                        dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                            h1
                                        ),
                                        dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                            h1
                                        )
                                    );
                                let len2: u64 =
                                    argument_as_uint64(
                                        dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                            h2
                                        ),
                                        dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                            h2
                                        )
                                    );
                                if len != len2
                                { false }
                                else if
                                mt11 == cbor_major_type_byte_string
                                ||
                                mt11 == cbor_major_type_text_string
                                {
                                    let cmp: i16 = lex_compare_bytes(lc1, lc2);
                                    cmp == 0i16
                                }
                                else
                                { mt11 != cbor_major_type_map }
                            };
                        if __anf0
                        {
                            (&mut pn)[0] = n·;
                            (&mut pl1)[0] = tl1·;
                            (&mut pl2)[0] = tl2·
                        }
                        else
                        { (&mut pres)[0] = option__bool::Some { v: false } }
                    }
                }
            };
            let res0: option__bool = (&pres)[0];
            let n0: usize = (&pn)[0];
            cond = eq_Some_true(res0) && n0 > 0usize
        };
        (&pres)[0]
    }
}

fn impl_check_equiv_basic(map_bound: option__size_t, l1: &[u8], l2: &[u8]) -> option__bool
{ impl_check_equiv_list_basic(map_bound, 1usize, l1, 1usize, l2) }

fn impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow_basic(
    nl1: usize,
    l1: &[u8],
    nl2: usize,
    l2: &[u8]
) ->
    option__bool
{
    let mut pl: [&[u8]; 1] = [l2; 1usize];
    let mut pn: [usize; 1] = [nl2; 1usize];
    let mut pres: [option__bool; 1] = [option__bool::Some { v: true }; 1usize];
    let n: usize = (&pn)[0];
    let res: option__bool = (&pres)[0];
    let mut cond: bool = n > 0usize && eq_Some_true(res);
    while
    cond
    {
        let l: &[u8] = (&pl)[0];
        let n0: usize = (&pn)[0];
        let n·: usize = n0.wrapping_sub(1usize);
        let i: usize = jump_raw_data_item(l, 0usize);
        let s: (&[u8], &[u8]) = l.split_at(i);
        let _letpattern: (&[u8], &[u8]) =
            {
                let s1: &[u8] = s.0;
                let s2: &[u8] = s.1;
                (s1,s2)
            };
        let _letpattern0: (&[u8], &[u8]) =
            {
                let input1: &[u8] = _letpattern.0;
                let input2: &[u8] = _letpattern.1;
                (input1,input2)
            };
        let _letpattern1: (&[u8], &[u8]) =
            {
                let input1: &[u8] = _letpattern0.0;
                let input2: &[u8] = _letpattern0.1;
                (input1,input2)
            };
        let _letpattern2: (&[u8], &[u8]) =
            {
                let left: &[u8] = _letpattern1.0;
                let right: &[u8] = _letpattern1.1;
                (left,right)
            };
        {
            let lh: &[u8] = _letpattern2.0;
            let lt: &[u8] = _letpattern2.1;
            let i0: usize = jump_raw_data_item(lt, 0usize);
            let s0: (&[u8], &[u8]) = lt.split_at(i0);
            let _letpattern10: (&[u8], &[u8]) =
                {
                    let s1: &[u8] = s0.0;
                    let s2: &[u8] = s0.1;
                    (s1,s2)
                };
            let _letpattern11: (&[u8], &[u8]) =
                {
                    let input1: &[u8] = _letpattern10.0;
                    let input2: &[u8] = _letpattern10.1;
                    (input1,input2)
                };
            let _letpattern12: (&[u8], &[u8]) =
                {
                    let input1: &[u8] = _letpattern11.0;
                    let input2: &[u8] = _letpattern11.1;
                    (input1,input2)
                };
            let _letpattern13: (&[u8], &[u8]) =
                {
                    let left: &[u8] = _letpattern12.0;
                    let right: &[u8] = _letpattern12.1;
                    (left,right)
                };
            let lv: &[u8] = _letpattern13.0;
            let lt·: &[u8] = _letpattern13.1;
            let mut pll: [&[u8]; 1] = [l1; 1usize];
            let mut pn1: [usize; 1] = [nl1; 1usize];
            let mut pres1: [option__bool; 1] = [option__bool::Some { v: false }; 1usize];
            let mut pcont: [bool; 1] = [true; 1usize];
            let n1: usize = (&pn1)[0];
            let res0: option__bool = (&pres1)[0];
            let cont: bool = (&pcont)[0];
            let mut cond0: bool = n1 > 0usize && eq_Some_false(res0) && cont;
            while
            cond0
            {
                let l3: &[u8] = (&pll)[0];
                let n10: usize = (&pn1)[0];
                let n·1: usize = n10.wrapping_sub(1usize);
                let i1: usize = jump_raw_data_item(l3, 0usize);
                let s1: (&[u8], &[u8]) = l3.split_at(i1);
                let _letpattern20: (&[u8], &[u8]) =
                    {
                        let s10: &[u8] = s1.0;
                        let s2: &[u8] = s1.1;
                        (s10,s2)
                    };
                let _letpattern21: (&[u8], &[u8]) =
                    {
                        let input1: &[u8] = _letpattern20.0;
                        let input2: &[u8] = _letpattern20.1;
                        (input1,input2)
                    };
                let _letpattern22: (&[u8], &[u8]) =
                    {
                        let input1: &[u8] = _letpattern21.0;
                        let input2: &[u8] = _letpattern21.1;
                        (input1,input2)
                    };
                let _letpattern23: (&[u8], &[u8]) =
                    {
                        let left: &[u8] = _letpattern22.0;
                        let right: &[u8] = _letpattern22.1;
                        (left,right)
                    };
                {
                    let lh1: &[u8] = _letpattern23.0;
                    let lt1: &[u8] = _letpattern23.1;
                    let res1: option__bool = impl_check_equiv_basic(option__size_t::None, lh, lh1);
                    if uu___is_None__bool(res1)
                    { (&mut pres1)[0] = res1 }
                    else
                    {
                        let i2: usize = jump_raw_data_item(lt1, 0usize);
                        let s2: (&[u8], &[u8]) = lt1.split_at(i2);
                        let _letpattern3: (&[u8], &[u8]) =
                            {
                                let s10: &[u8] = s2.0;
                                let s20: &[u8] = s2.1;
                                (s10,s20)
                            };
                        let _letpattern30: (&[u8], &[u8]) =
                            {
                                let input1: &[u8] = _letpattern3.0;
                                let input2: &[u8] = _letpattern3.1;
                                (input1,input2)
                            };
                        let _letpattern31: (&[u8], &[u8]) =
                            {
                                let input1: &[u8] = _letpattern30.0;
                                let input2: &[u8] = _letpattern30.1;
                                (input1,input2)
                            };
                        let _letpattern32: (&[u8], &[u8]) =
                            {
                                let left: &[u8] = _letpattern31.0;
                                let right: &[u8] = _letpattern31.1;
                                (left,right)
                            };
                        let lv1: &[u8] = _letpattern32.0;
                        let lt·1: &[u8] = _letpattern32.1;
                        if
                        match res1
                        {
                            option__bool::Some { v } => v,
                            _ => panic!("Incomplete pattern matching")
                        }
                        {
                            let __anf0: option__bool =
                                impl_check_equiv_basic(option__size_t::None, lv, lv1);
                            (&mut pres1)[0] = __anf0;
                            (&mut pcont)[0] = false
                        }
                        else
                        {
                            (&mut pll)[0] = lt·1;
                            (&mut pn1)[0] = n·1
                        }
                    }
                };
                let n11: usize = (&pn1)[0];
                let res1: option__bool = (&pres1)[0];
                let cont0: bool = (&pcont)[0];
                cond0 = n11 > 0usize && eq_Some_false(res1) && cont0
            };
            let res1: option__bool = (&pres1)[0];
            if eq_Some_true(res1)
            {
                (&mut pl)[0] = lt·;
                (&mut pn)[0] = n·
            }
            else
            { (&mut pres)[0] = res1 }
        };
        let n1: usize = (&pn)[0];
        let res0: option__bool = (&pres)[0];
        cond = n1 > 0usize && eq_Some_true(res0)
    };
    (&pres)[0]
}

fn impl_check_valid_basic(map_bound: option__size_t, strict_bound_check: bool, l1: &[u8]) ->
    bool
{
    let mut pn: [usize; 1] = [1usize; 1usize];
    let mut pres: [bool; 1] = [true; 1usize];
    let mut ppi: [&[u8]; 1] = [l1; 1usize];
    let res: bool = (&pres)[0];
    let n: usize = (&pn)[0];
    let mut cond: bool = res && n > 0usize;
    while
    cond
    {
        let n0: usize = (&pn)[0];
        let pi: &[u8] = (&ppi)[0];
        let i: usize = jump_header(pi, 0usize);
        let s: (&[u8], &[u8]) = pi.split_at(i);
        let _letpattern: (&[u8], &[u8]) =
            {
                let s1: &[u8] = s.0;
                let s2: &[u8] = s.1;
                (s1,s2)
            };
        let _letpattern0: (&[u8], &[u8]) =
            {
                let input1: &[u8] = _letpattern.0;
                let input2: &[u8] = _letpattern.1;
                (input1,input2)
            };
        let _letpattern1: (&[u8], &[u8]) =
            {
                let input1: &[u8] = _letpattern0.0;
                let input2: &[u8] = _letpattern0.1;
                (input1,input2)
            };
        let _letpattern2: (&[u8], &[u8]) =
            {
                let left: &[u8] = _letpattern1.0;
                let right: &[u8] = _letpattern1.1;
                (left,right)
            };
        let res0: bool =
            {
                let ah: &[u8] = _letpattern2.0;
                let _a1: &[u8] = _letpattern2.1;
                let h: header = read_header(ah);
                if get_header_major_type(h) == cbor_major_type_map
                {
                    let i0: usize = jump_raw_data_item(pi, 0usize);
                    let s0: (&[u8], &[u8]) = pi.split_at(i0);
                    let _letpattern10: (&[u8], &[u8]) =
                        {
                            let s1: &[u8] = s0.0;
                            let s2: &[u8] = s0.1;
                            (s1,s2)
                        };
                    let _letpattern11: (&[u8], &[u8]) =
                        {
                            let input1: &[u8] = _letpattern10.0;
                            let input2: &[u8] = _letpattern10.1;
                            (input1,input2)
                        };
                    let _letpattern12: (&[u8], &[u8]) =
                        {
                            let input1: &[u8] = _letpattern11.0;
                            let input2: &[u8] = _letpattern11.1;
                            (input1,input2)
                        };
                    let hd: &[u8] =
                        {
                            let input1: &[u8] = _letpattern12.0;
                            let _input2: &[u8] = _letpattern12.1;
                            input1
                        };
                    let mut ph: [header; 1] = [h; 1usize];
                    let i1: usize = jump_header(hd, 0usize);
                    let s1: (&[u8], &[u8]) = hd.split_at(i1);
                    let _letpattern13: (&[u8], &[u8]) =
                        {
                            let s10: &[u8] = s1.0;
                            let s2: &[u8] = s1.1;
                            (s10,s2)
                        };
                    let _letpattern14: (&[u8], &[u8]) =
                        {
                            let input1: &[u8] = _letpattern13.0;
                            let input2: &[u8] = _letpattern13.1;
                            (input1,input2)
                        };
                    let c: &[u8] =
                        {
                            let ph1: &[u8] = _letpattern14.0;
                            let outc: &[u8] = _letpattern14.1;
                            let h1: header = read_header(ph1);
                            (&mut ph)[0] = h1;
                            outc
                        };
                    let mut pl: [&[u8]; 1] = [c; 1usize];
                    let mut pn1: [usize; 1] =
                        [argument_as_uint64(
                                dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                    h
                                ),
                                dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(
                                    h
                                )
                            )
                            as
                            usize;
                            1usize];
                    let mut pres1: [option__bool; 1] = [option__bool::Some { v: true }; 1usize];
                    let n1: usize = (&pn1)[0];
                    let res0: option__bool = (&pres1)[0];
                    let mut cond0: bool = n1 > 0usize && eq_Some_true(res0);
                    while
                    cond0
                    {
                        let n10: usize = (&pn1)[0];
                        let n·: usize = n10.wrapping_sub(1usize);
                        let l: &[u8] = (&pl)[0];
                        let i2: usize = jump_raw_data_item(l, 0usize);
                        let s2: (&[u8], &[u8]) = l.split_at(i2);
                        let _letpattern15: (&[u8], &[u8]) =
                            {
                                let s10: &[u8] = s2.0;
                                let s20: &[u8] = s2.1;
                                (s10,s20)
                            };
                        let _letpattern16: (&[u8], &[u8]) =
                            {
                                let input1: &[u8] = _letpattern15.0;
                                let input2: &[u8] = _letpattern15.1;
                                (input1,input2)
                            };
                        let _letpattern17: (&[u8], &[u8]) =
                            {
                                let input1: &[u8] = _letpattern16.0;
                                let input2: &[u8] = _letpattern16.1;
                                (input1,input2)
                            };
                        let _letpattern18: (&[u8], &[u8]) =
                            {
                                let left: &[u8] = _letpattern17.0;
                                let right: &[u8] = _letpattern17.1;
                                (left,right)
                            };
                        {
                            let lh: &[u8] = _letpattern18.0;
                            let lt: &[u8] = _letpattern18.1;
                            let i3: usize = jump_raw_data_item(lt, 0usize);
                            let s3: (&[u8], &[u8]) = lt.split_at(i3);
                            let _letpattern20: (&[u8], &[u8]) =
                                {
                                    let s10: &[u8] = s3.0;
                                    let s20: &[u8] = s3.1;
                                    (s10,s20)
                                };
                            let _letpattern21: (&[u8], &[u8]) =
                                {
                                    let input1: &[u8] = _letpattern20.0;
                                    let input2: &[u8] = _letpattern20.1;
                                    (input1,input2)
                                };
                            let _letpattern22: (&[u8], &[u8]) =
                                {
                                    let input1: &[u8] = _letpattern21.0;
                                    let input2: &[u8] = _letpattern21.1;
                                    (input1,input2)
                                };
                            let _letpattern23: (&[u8], &[u8]) =
                                {
                                    let left: &[u8] = _letpattern22.0;
                                    let right: &[u8] = _letpattern22.1;
                                    (left,right)
                                };
                            let _lv: &[u8] = _letpattern23.0;
                            let lt·: &[u8] = _letpattern23.1;
                            let mut pl1: [&[u8]; 1] = [lt·; 1usize];
                            let mut pn2: [usize; 1] = [n·; 1usize];
                            let mut pres2: [option__bool; 1] =
                                [option__bool::Some { v: false }; 1usize];
                            let n2: usize = (&pn2)[0];
                            let res1: option__bool = (&pres2)[0];
                            let mut cond1: bool = n2 > 0usize && eq_Some_false(res1);
                            while
                            cond1
                            {
                                let n20: usize = (&pn2)[0];
                                let n·1: usize = n20.wrapping_sub(1usize);
                                let l2: &[u8] = (&pl1)[0];
                                let i4: usize = jump_raw_data_item(l2, 0usize);
                                let s4: (&[u8], &[u8]) = l2.split_at(i4);
                                let _letpattern3: (&[u8], &[u8]) =
                                    {
                                        let s10: &[u8] = s4.0;
                                        let s20: &[u8] = s4.1;
                                        (s10,s20)
                                    };
                                let _letpattern30: (&[u8], &[u8]) =
                                    {
                                        let input1: &[u8] = _letpattern3.0;
                                        let input2: &[u8] = _letpattern3.1;
                                        (input1,input2)
                                    };
                                let _letpattern31: (&[u8], &[u8]) =
                                    {
                                        let input1: &[u8] = _letpattern30.0;
                                        let input2: &[u8] = _letpattern30.1;
                                        (input1,input2)
                                    };
                                let _letpattern32: (&[u8], &[u8]) =
                                    {
                                        let left: &[u8] = _letpattern31.0;
                                        let right: &[u8] = _letpattern31.1;
                                        (left,right)
                                    };
                                {
                                    let lh1: &[u8] = _letpattern32.0;
                                    let lt1: &[u8] = _letpattern32.1;
                                    let res2: option__bool =
                                        impl_check_equiv_basic(map_bound, lh, lh1);
                                    if eq_Some_false(res2)
                                    {
                                        let i5: usize = jump_raw_data_item(lt1, 0usize);
                                        let s5: (&[u8], &[u8]) = lt1.split_at(i5);
                                        let _letpattern4: (&[u8], &[u8]) =
                                            {
                                                let s10: &[u8] = s5.0;
                                                let s20: &[u8] = s5.1;
                                                (s10,s20)
                                            };
                                        let _letpattern40: (&[u8], &[u8]) =
                                            {
                                                let input1: &[u8] = _letpattern4.0;
                                                let input2: &[u8] = _letpattern4.1;
                                                (input1,input2)
                                            };
                                        let _letpattern41: (&[u8], &[u8]) =
                                            {
                                                let input1: &[u8] = _letpattern40.0;
                                                let input2: &[u8] = _letpattern40.1;
                                                (input1,input2)
                                            };
                                        let _letpattern42: (&[u8], &[u8]) =
                                            {
                                                let left: &[u8] = _letpattern41.0;
                                                let right: &[u8] = _letpattern41.1;
                                                (left,right)
                                            };
                                        let _lv1: &[u8] = _letpattern42.0;
                                        let lt·1: &[u8] = _letpattern42.1;
                                        (&mut pl1)[0] = lt·1;
                                        (&mut pn2)[0] = n·1
                                    }
                                    else
                                    { (&mut pres2)[0] = res2 }
                                };
                                let n21: usize = (&pn2)[0];
                                let res2: option__bool = (&pres2)[0];
                                cond1 = n21 > 0usize && eq_Some_false(res2)
                            };
                            let res2: option__bool = (&pres2)[0];
                            if uu___is_None__bool(res2)
                            { (&mut pres1)[0] = option__bool::None }
                            else if
                            match res2
                            {
                                option__bool::Some { v } => v,
                                _ => panic!("Incomplete pattern matching")
                            }
                            { (&mut pres1)[0] = option__bool::Some { v: false } }
                            else
                            {
                                let ite: option__size_t =
                                    if strict_bound_check
                                    { map_bound }
                                    else
                                    { option__size_t::None };
                                let __anf0: bool = impl_check_map_depth_opt(ite, 1usize, lh);
                                if __anf0
                                {
                                    (&mut pn1)[0] = n·;
                                    (&mut pl)[0] = lt·
                                }
                                else
                                { (&mut pres1)[0] = option__bool::None }
                            }
                        };
                        let n11: usize = (&pn1)[0];
                        let res1: option__bool = (&pres1)[0];
                        cond0 = n11 > 0usize && eq_Some_true(res1)
                    };
                    let res1: option__bool = (&pres1)[0];
                    eq_Some_true(res1)
                }
                else
                { true }
            };
        if ! res0
        { (&mut pres)[0] = false }
        else
        {
            let off1: usize = jump_header(pi, 0usize);
            let s·: (&[u8], &[u8]) = pi.split_at(0usize);
            let _letpattern3: (&[u8], &[u8]) =
                {
                    let s1: &[u8] = s·.0;
                    let s2: &[u8] = s·.1;
                    (s1,s2)
                };
            let input·: &[u8] =
                {
                    let _input1: &[u8] = _letpattern3.0;
                    let input23: &[u8] = _letpattern3.1;
                    let consumed: usize = off1.wrapping_sub(0usize);
                    let _letpattern10: (&[u8], &[u8]) = input23.split_at(consumed);
                    let _letpattern11: (&[u8], &[u8]) =
                        {
                            let s1: &[u8] = _letpattern10.0;
                            let s2: &[u8] = _letpattern10.1;
                            (s1,s2)
                        };
                    let _letpattern12: (&[u8], &[u8]) =
                        {
                            let left: &[u8] = _letpattern11.0;
                            let right: &[u8] = _letpattern11.1;
                            (left,right)
                        };
                    let input2: &[u8] = _letpattern12.0;
                    let _input3: &[u8] = _letpattern12.1;
                    input2
                };
            let x: header = read_header(input·);
            let b: initial_byte_t = x.fst;
            let i0: usize =
                if
                b.major_type == cbor_major_type_byte_string
                ||
                b.major_type == cbor_major_type_text_string
                {
                    let b0: initial_byte_t = x.fst;
                    let l: long_argument = x.snd;
                    off1.wrapping_add(argument_as_uint64(b0, l) as usize)
                }
                else
                { off1.wrapping_add(0usize) };
            let s0: (&[u8], &[u8]) = pi.split_at(i0);
            let _letpattern4: (&[u8], &[u8]) =
                {
                    let s1: &[u8] = s0.0;
                    let s2: &[u8] = s0.1;
                    (s1,s2)
                };
            let _letpattern5: (&[u8], &[u8]) =
                {
                    let input1: &[u8] = _letpattern4.0;
                    let input2: &[u8] = _letpattern4.1;
                    (input1,input2)
                };
            let ph: &[u8] = _letpattern5.0;
            let pc: &[u8] = _letpattern5.1;
            let unused: usize = pc.len();
            crate::lowstar::ignore::ignore::<usize>(unused);
            let count: usize = jump_recursive_step_count_leaf(ph);
            let n·: usize = n0.wrapping_sub(1usize).wrapping_add(count);
            (&mut pn)[0] = n·;
            (&mut ppi)[0] = pc
        };
        let res1: bool = (&pres)[0];
        let n1: usize = (&pn)[0];
        cond = res1 && n1 > 0usize
    };
    (&pres)[0]
}

fn cbor_validate_nondet(map_key_bound: option__size_t, strict_check: bool, input: &[u8]) ->
    usize
{
    let mut poff: [usize; 1] = [0usize; 1usize];
    let res: bool = validate_raw_data_item(input, &mut poff);
    if res
    {
        let off: usize = (&poff)[0];
        let s·: (&[u8], &[u8]) = input.split_at(0usize);
        let _letpattern: (&[u8], &[u8]) =
            {
                let s1: &[u8] = s·.0;
                let s2: &[u8] = s·.1;
                (s1,s2)
            };
        let input·: &[u8] =
            {
                let _input1: &[u8] = _letpattern.0;
                let input23: &[u8] = _letpattern.1;
                let consumed: usize = off.wrapping_sub(0usize);
                let _letpattern1: (&[u8], &[u8]) = input23.split_at(consumed);
                let _letpattern10: (&[u8], &[u8]) =
                    {
                        let s1: &[u8] = _letpattern1.0;
                        let s2: &[u8] = _letpattern1.1;
                        (s1,s2)
                    };
                let _letpattern11: (&[u8], &[u8]) =
                    {
                        let left: &[u8] = _letpattern10.0;
                        let right: &[u8] = _letpattern10.1;
                        (left,right)
                    };
                let input2: &[u8] = _letpattern11.0;
                let _input3: &[u8] = _letpattern11.1;
                input2
            };
        let res1: bool = impl_check_valid_basic(map_key_bound, strict_check, input·);
        if res1 { off } else { 0usize }
    }
    else
    { 0usize }
}

fn cbor_match_equal_serialized_tagged(c1: cbor_serialized, c2: cbor_serialized) -> bool
{
    if c1.cbor_serialized_header.value != c2.cbor_serialized_header.value
    { false }
    else
    {
        let res: option__bool =
            impl_check_equiv_basic(
                option__size_t::None,
                c1.cbor_serialized_payload,
                c2.cbor_serialized_payload
            );
        eq_Some_true(res)
    }
}

fn cbor_match_compare_serialized_array(c1: cbor_serialized, c2: cbor_serialized) -> bool
{
    let n1: usize = c1.cbor_serialized_header.value as usize;
    let n2: usize = c2.cbor_serialized_header.value as usize;
    let res: option__bool =
        impl_check_equiv_list_basic(
            option__size_t::None,
            n1,
            c1.cbor_serialized_payload,
            n2,
            c2.cbor_serialized_payload
        );
    eq_Some_true(res)
}

fn cbor_match_compare_serialized_map(c1: cbor_serialized, c2: cbor_serialized) -> bool
{
    let n1: usize = c1.cbor_serialized_header.value as usize;
    let n2: usize = c2.cbor_serialized_header.value as usize;
    let res21: option__bool =
        impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow_basic(
            n2,
            c2.cbor_serialized_payload,
            n1,
            c1.cbor_serialized_payload
        );
    if eq_Some_true(res21)
    {
        let res12: option__bool =
            impl_list_for_all_with_overflow_setoid_assoc_eq_with_overflow_basic(
                n1,
                c1.cbor_serialized_payload,
                n2,
                c2.cbor_serialized_payload
            );
        eq_Some_true(res12)
    }
    else
    { false }
}

fn uu___is_Some__bool(projectee: option__bool) -> bool
{ match projectee { option__bool::Some { .. } => true, _ => false } }

pub(crate) fn cbor_nondet_equiv(x1: cbor_raw, x2: cbor_raw) -> bool
{
    let mt1: u8 = impl_major_type(x1);
    let mt2: u8 = impl_major_type(x2);
    if mt1 != mt2
    { false }
    else if mt1 == cbor_major_type_simple_value
    {
        let _letpattern: cbor_raw = x1;
        let w1: u8 =
            match _letpattern
            {
                cbor_raw::CBOR_Case_Simple { v: res } => res,
                _ => panic!("Incomplete pattern matching")
            };
        let _letpattern0: cbor_raw = x2;
        let w2: u8 =
            match _letpattern0
            {
                cbor_raw::CBOR_Case_Simple { v: res } => res,
                _ => panic!("Incomplete pattern matching")
            };
        w1 == w2
    }
    else if mt1 == cbor_major_type_uint64 || mt1 == cbor_major_type_neg_int64
    {
        let _letpattern: cbor_raw = x1;
        let w1: raw_uint64 =
            match _letpattern
            {
                cbor_raw::CBOR_Case_Int { v: c· } =>
                  raw_uint64 { size: c·.cbor_int_size, value: c·.cbor_int_value },
                _ => panic!("Incomplete pattern matching")
            };
        let _letpattern0: cbor_raw = x2;
        let w2: raw_uint64 =
            match _letpattern0
            {
                cbor_raw::CBOR_Case_Int { v: c· } =>
                  raw_uint64 { size: c·.cbor_int_size, value: c·.cbor_int_value },
                _ => panic!("Incomplete pattern matching")
            };
        w1.value == w2.value
    }
    else if mt1 == cbor_major_type_byte_string || mt1 == cbor_major_type_text_string
    {
        let _letpattern: cbor_raw = x1;
        let len1: raw_uint64 =
            match _letpattern
            {
                cbor_raw::CBOR_Case_String { v: c· } =>
                  raw_uint64
                  { size: c·.cbor_string_size, value: (c·.cbor_string_ptr).len() as u64 },
                _ => panic!("Incomplete pattern matching")
            };
        let _letpattern0: cbor_raw = x2;
        let len2: raw_uint64 =
            match _letpattern0
            {
                cbor_raw::CBOR_Case_String { v: c· } =>
                  raw_uint64
                  { size: c·.cbor_string_size, value: (c·.cbor_string_ptr).len() as u64 },
                _ => panic!("Incomplete pattern matching")
            };
        if len1.value != len2.value
        { false }
        else
        {
            let _letpattern1: cbor_raw = x1;
            let w1: &[u8] =
                match _letpattern1
                {
                    cbor_raw::CBOR_Case_String { v: c· } => c·.cbor_string_ptr,
                    _ => panic!("Incomplete pattern matching")
                };
            let _letpattern2: cbor_raw = x2;
            let w2: &[u8] =
                match _letpattern2
                {
                    cbor_raw::CBOR_Case_String { v: c· } => c·.cbor_string_ptr,
                    _ => panic!("Incomplete pattern matching")
                };
            let res: i16 = lex_compare_bytes(w1, w2);
            res == 0i16
        }
    }
    else if mt1 == cbor_major_type_tagged
    {
        if
        match (x1,x2)
        {
            (
                cbor_raw::CBOR_Case_Serialized_Tagged
                { .. },cbor_raw::CBOR_Case_Serialized_Tagged
                { .. }
            )
            => true,
            _ => false
        }
        {
            let _letpattern: cbor_raw = x1;
            match _letpattern
            {
                cbor_raw::CBOR_Case_Serialized_Tagged { v: cs1 } =>
                  {
                      let _letpattern1: cbor_raw = x2;
                      match _letpattern1
                      {
                          cbor_raw::CBOR_Case_Serialized_Tagged { v: cs2 } =>
                            cbor_match_equal_serialized_tagged(cs1, cs2),
                          _ => panic!("Incomplete pattern matching")
                      }
                  },
                _ => panic!("Incomplete pattern matching")
            }
        }
        else
        {
            let tag1: raw_uint64 =
                match x1
                {
                    cbor_raw::CBOR_Case_Tagged { v: c· } => c·.cbor_tagged_tag,
                    cbor_raw::CBOR_Case_Serialized_Tagged { v: c· } => c·.cbor_serialized_header,
                    _ => panic!("Incomplete pattern matching")
                };
            let tag2: raw_uint64 =
                match x2
                {
                    cbor_raw::CBOR_Case_Tagged { v: c· } => c·.cbor_tagged_tag,
                    cbor_raw::CBOR_Case_Serialized_Tagged { v: c· } => c·.cbor_serialized_header,
                    _ => panic!("Incomplete pattern matching")
                };
            if tag1.value != tag2.value
            { false }
            else
            {
                let w1: cbor_raw = cbor_match_tagged_get_payload(x1);
                let w2: cbor_raw = cbor_match_tagged_get_payload(x2);
                cbor_nondet_equiv(w1, w2)
            }
        }
    }
    else if mt1 == cbor_major_type_array
    {
        if
        match (x1,x2)
        {
            (
                cbor_raw::CBOR_Case_Serialized_Array
                { .. },cbor_raw::CBOR_Case_Serialized_Array
                { .. }
            )
            => true,
            _ => false
        }
        {
            let _letpattern: cbor_raw = x1;
            match _letpattern
            {
                cbor_raw::CBOR_Case_Serialized_Array { v: cs1 } =>
                  {
                      let _letpattern1: cbor_raw = x2;
                      match _letpattern1
                      {
                          cbor_raw::CBOR_Case_Serialized_Array { v: cs2 } =>
                            cbor_match_compare_serialized_array(cs1, cs2),
                          _ => panic!("Incomplete pattern matching")
                      }
                  },
                _ => panic!("Incomplete pattern matching")
            }
        }
        else
        {
            let len1: raw_uint64 =
                match x1
                {
                    cbor_raw::CBOR_Case_Array { v: c· } =>
                      raw_uint64
                      { size: c·.cbor_array_length_size, value: (c·.cbor_array_ptr).len() as u64 },
                    cbor_raw::CBOR_Case_Serialized_Array { v: c· } => c·.cbor_serialized_header,
                    _ => panic!("Incomplete pattern matching")
                };
            let len2: raw_uint64 =
                match x2
                {
                    cbor_raw::CBOR_Case_Array { v: c· } =>
                      raw_uint64
                      { size: c·.cbor_array_length_size, value: (c·.cbor_array_ptr).len() as u64 },
                    cbor_raw::CBOR_Case_Serialized_Array { v: c· } => c·.cbor_serialized_header,
                    _ => panic!("Incomplete pattern matching")
                };
            if len1.value != len2.value
            { false }
            else
            {
                let i1: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    cbor_array_iterator_init(x1);
                let i2: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    cbor_array_iterator_init(x2);
                let mut pi1: [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] = [i1; 1usize];
                let mut pi2: [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] = [i2; 1usize];
                let mut pres: [bool; 1] = [true; 1usize];
                let __anf0: bool = (&pres)[0];
                let mut cond: bool =
                    if __anf0
                    {
                        let i11: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pi1)[0];
                        let __anf01: bool = cbor_array_iterator_is_empty(i11);
                        ! __anf01
                    }
                    else
                    { false };
                while
                cond
                {
                    let y1: cbor_raw = cbor_array_iterator_next(&mut pi1);
                    let y2: cbor_raw = cbor_array_iterator_next(&mut pi2);
                    let __anf00: bool = cbor_nondet_equiv(y1, y2);
                    (&mut pres)[0] = __anf00;
                    let __anf01: bool = (&pres)[0];
                    let ite: bool =
                        if __anf01
                        {
                            let i11: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pi1)[0];
                            let __anf010: bool = cbor_array_iterator_is_empty(i11);
                            ! __anf010
                        }
                        else
                        { false };
                    cond = ite
                };
                (&pres)[0]
            }
        }
    }
    else if
    match (x1,x2)
    {
        (cbor_raw::CBOR_Case_Serialized_Map { .. },cbor_raw::CBOR_Case_Serialized_Map { .. }) =>
          true,
        _ => false
    }
    {
        let _letpattern: cbor_raw = x1;
        match _letpattern
        {
            cbor_raw::CBOR_Case_Serialized_Map { v: cs1 } =>
              {
                  let _letpattern1: cbor_raw = x2;
                  match _letpattern1
                  {
                      cbor_raw::CBOR_Case_Serialized_Map { v: cs2 } =>
                        cbor_match_compare_serialized_map(cs1, cs2),
                      _ => panic!("Incomplete pattern matching")
                  }
              },
            _ => panic!("Incomplete pattern matching")
        }
    }
    else
    {
        let i1: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry = cbor_map_iterator_init(x1);
        let i2: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry = cbor_map_iterator_init(x2);
        let mut pi2: [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry; 1] = [i1; 1usize];
        let mut pres: [bool; 1] = [true; 1usize];
        let __anf0: bool = (&pres)[0];
        let mut cond: bool =
            if __anf0
            {
                let i21: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry = (&pi2)[0];
                let __anf01: bool = cbor_map_iterator_is_empty(i21);
                ! __anf01
            }
            else
            { false };
        while
        cond
        {
            let x21: cbor_map_entry = cbor_map_iterator_next(&mut pi2);
            let mut pi1: [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry; 1] = [i2; 1usize];
            let mut pres1: [option__bool; 1] = [option__bool::None; 1usize];
            let __anf00: option__bool = (&pres1)[0];
            let mut cond0: bool =
                if uu___is_Some__bool(__anf00)
                { false }
                else
                {
                    let i11: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry = (&pi1)[0];
                    let __anf01: bool = cbor_map_iterator_is_empty(i11);
                    ! __anf01
                };
            while
            cond0
            {
                let x11: cbor_map_entry = cbor_map_iterator_next(&mut pi1);
                let __anf01: bool =
                    cbor_nondet_equiv(x21.cbor_map_entry_key, x11.cbor_map_entry_key);
                if __anf01
                {
                    let __anf010: bool =
                        cbor_nondet_equiv(x21.cbor_map_entry_value, x11.cbor_map_entry_value);
                    (&mut pres1)[0] = option__bool::Some { v: __anf010 }
                };
                let __anf02: option__bool = (&pres1)[0];
                let ite: bool =
                    if uu___is_Some__bool(__anf02)
                    { false }
                    else
                    {
                        let i11: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry = (&pi1)[0];
                        let __anf010: bool = cbor_map_iterator_is_empty(i11);
                        ! __anf010
                    };
                cond0 = ite
            };
            let __anf01: option__bool = (&pres1)[0];
            let __anf02: bool = eq_Some_true(__anf01);
            (&mut pres)[0] = __anf02;
            let __anf03: bool = (&pres)[0];
            let ite: bool =
                if __anf03
                {
                    let i21: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry = (&pi2)[0];
                    let __anf010: bool = cbor_map_iterator_is_empty(i21);
                    ! __anf010
                }
                else
                { false };
            cond = ite
        };
        let __anf00: bool = (&pres)[0];
        if ! __anf00
        { false }
        else
        {
            let mut pi20: [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry; 1] = [i2; 1usize];
            let mut pres0: [bool; 1] = [true; 1usize];
            let __anf01: bool = (&pres0)[0];
            let mut cond0: bool =
                if __anf01
                {
                    let i21: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry = (&pi20)[0];
                    let __anf02: bool = cbor_map_iterator_is_empty(i21);
                    ! __anf02
                }
                else
                { false };
            while
            cond0
            {
                let x21: cbor_map_entry = cbor_map_iterator_next(&mut pi20);
                let mut pi1: [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry; 1] =
                    [i1; 1usize];
                let mut pres1: [option__bool; 1] = [option__bool::None; 1usize];
                let __anf010: option__bool = (&pres1)[0];
                let mut cond1: bool =
                    if uu___is_Some__bool(__anf010)
                    { false }
                    else
                    {
                        let i11: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry = (&pi1)[0];
                        let __anf02: bool = cbor_map_iterator_is_empty(i11);
                        ! __anf02
                    };
                while
                cond1
                {
                    let x11: cbor_map_entry = cbor_map_iterator_next(&mut pi1);
                    let __anf011: bool =
                        cbor_nondet_equiv(x21.cbor_map_entry_key, x11.cbor_map_entry_key);
                    if __anf011
                    {
                        let __anf02: bool =
                            cbor_nondet_equiv(x21.cbor_map_entry_value, x11.cbor_map_entry_value);
                        (&mut pres1)[0] = option__bool::Some { v: __anf02 }
                    };
                    let __anf012: option__bool = (&pres1)[0];
                    let ite: bool =
                        if uu___is_Some__bool(__anf012)
                        { false }
                        else
                        {
                            let i11: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
                                (&pi1)[0];
                            let __anf02: bool = cbor_map_iterator_is_empty(i11);
                            ! __anf02
                        };
                    cond1 = ite
                };
                let __anf011: option__bool = (&pres1)[0];
                let __anf012: bool = eq_Some_true(__anf011);
                (&mut pres0)[0] = __anf012;
                let __anf013: bool = (&pres0)[0];
                let ite: bool =
                    if __anf013
                    {
                        let i21: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry = (&pi20)[0];
                        let __anf02: bool = cbor_map_iterator_is_empty(i21);
                        ! __anf02
                    }
                    else
                    { false };
                cond0 = ite
            };
            (&pres0)[0]
        }
    }
}

fn cbor_nondet_no_setoid_repeats(x: &[cbor_map_entry]) -> bool
{
    let mut pn1: [usize; 1] = [0usize; 1usize];
    let mut pres: [bool; 1] = [true; 1usize];
    let __anf0: bool = (&pres)[0];
    let mut cond: bool =
        if __anf0
        {
            let __anf01: usize = (&pn1)[0];
            __anf01 < x.len()
        }
        else
        { false };
    while
    cond
    {
        let n1: usize = (&pn1)[0];
        let x1: cbor_map_entry = x[n1];
        let n2: usize = n1.wrapping_add(1usize);
        (&mut pn1)[0] = n2;
        let mut pn2: [usize; 1] = [n2; 1usize];
        let __anf00: bool = (&pres)[0];
        let mut cond0: bool =
            if __anf00
            {
                let __anf01: usize = (&pn2)[0];
                __anf01 < x.len()
            }
            else
            { false };
        while
        cond0
        {
            let n21: usize = (&pn2)[0];
            let x2: cbor_map_entry = x[n21];
            let __anf01: bool = cbor_nondet_equiv(x1.cbor_map_entry_key, x2.cbor_map_entry_key);
            (&mut pres)[0] = ! __anf01;
            (&mut pn2)[0] = n21.wrapping_add(1usize);
            let __anf02: bool = (&pres)[0];
            let ite: bool =
                if __anf02
                {
                    let __anf010: usize = (&pn2)[0];
                    __anf010 < x.len()
                }
                else
                { false };
            cond0 = ite
        };
        let __anf01: bool = (&pres)[0];
        let ite: bool =
            if __anf01
            {
                let __anf010: usize = (&pn1)[0];
                __anf010 < x.len()
            }
            else
            { false };
        cond = ite
    };
    (&pres)[0]
}

fn cbor_nondet_validate(map_key_bound: option__size_t, strict_check: bool, input: &[u8]) ->
    usize
{ cbor_validate_nondet(map_key_bound, strict_check, input) }

fn cbor_nondet_parse_valid <'a>(input: &'a [u8], len: usize) -> cbor_raw <'a>
{ cbor_parse(input, len) }

#[derive(PartialEq, Clone, Copy)]
pub enum option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (cbor_raw <'a>, &'a [u8]) }
}

pub(crate) fn cbor_nondet_parse <'a>(
    map_key_bound: option__size_t,
    strict_check: bool,
    input: &'a [u8]
) ->
    option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let len: usize = cbor_nondet_validate(map_key_bound, strict_check, input);
    if len == 0usize
    { option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None }
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
        let resl: cbor_raw = cbor_nondet_parse_valid(inl, len);
        option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: (resl,inr) }
    }
}

pub(crate) fn cbor_nondet_size(x: cbor_raw, bound: usize) -> usize { cbor_size(x, bound) }

pub(crate) fn cbor_nondet_serialize(x: cbor_raw, output: &mut [u8]) -> option__size_t
{
    let len: usize = cbor_size(x, output.len());
    if len == 0usize
    { option__size_t::None }
    else
    {
        let _letpattern: (&mut [u8], &mut [u8]) = output.split_at_mut(len);
        let out: &mut [u8] = _letpattern.0;
        let _outr: &[u8] = _letpattern.1;
        let res: usize = cbor_serialize(x, out);
        option__size_t::Some { v: res }
    }
}

pub(crate) fn cbor_nondet_major_type(x: cbor_raw) -> u8 { impl_major_type(x) }

pub(crate) fn cbor_nondet_read_simple_value(x: cbor_raw) -> u8
{
    let _letpattern: cbor_raw = x;
    match _letpattern
    { cbor_raw::CBOR_Case_Simple { v: res } => res, _ => panic!("Incomplete pattern matching") }
}

pub(crate) fn cbor_nondet_read_uint64(x: cbor_raw) -> u64
{
    let _letpattern: cbor_raw = x;
    let res: raw_uint64 =
        match _letpattern
        {
            cbor_raw::CBOR_Case_Int { v: c· } =>
              raw_uint64 { size: c·.cbor_int_size, value: c·.cbor_int_value },
            _ => panic!("Incomplete pattern matching")
        };
    res.value
}

pub(crate) fn cbor_nondet_get_string <'a>(x: cbor_raw <'a>) -> &'a [u8]
{
    let _letpattern: cbor_raw = x;
    match _letpattern
    {
        cbor_raw::CBOR_Case_String { v: c· } => c·.cbor_string_ptr,
        _ => panic!("Incomplete pattern matching")
    }
}

pub(crate) fn cbor_nondet_get_tagged_tag(x: cbor_raw) -> u64
{
    let res: raw_uint64 =
        match x
        {
            cbor_raw::CBOR_Case_Tagged { v: c· } => c·.cbor_tagged_tag,
            cbor_raw::CBOR_Case_Serialized_Tagged { v: c· } => c·.cbor_serialized_header,
            _ => panic!("Incomplete pattern matching")
        };
    res.value
}

pub(crate) fn cbor_nondet_get_tagged_payload <'a>(x: cbor_raw <'a>) -> cbor_raw <'a>
{ cbor_match_tagged_get_payload(x) }

pub(crate) fn cbor_nondet_get_array_length(x: cbor_raw) -> u64
{
    let res: raw_uint64 =
        match x
        {
            cbor_raw::CBOR_Case_Array { v: c· } =>
              raw_uint64
              { size: c·.cbor_array_length_size, value: (c·.cbor_array_ptr).len() as u64 },
            cbor_raw::CBOR_Case_Serialized_Array { v: c· } => c·.cbor_serialized_header,
            _ => panic!("Incomplete pattern matching")
        };
    res.value
}

pub(crate) fn cbor_nondet_array_iterator_start <'a>(x: cbor_raw <'a>) ->
    cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{ cbor_array_iterator_init(x) }

pub(crate) fn cbor_nondet_array_iterator_is_empty(
    x: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
) ->
    bool
{ cbor_array_iterator_is_empty(x) }

pub(crate) fn cbor_nondet_array_iterator_next <'b, 'a>(
    x: &'b mut [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>]
) ->
    cbor_raw
    <'a>
{ cbor_array_iterator_next(x) }

pub(crate) fn cbor_nondet_get_array_item <'a>(x: cbor_raw <'a>, i: u64) -> cbor_raw <'a>
{ cbor_array_item(x, i) }

pub(crate) fn cbor_nondet_get_map_length(x: cbor_raw) -> u64
{
    let res: raw_uint64 =
        match x
        {
            cbor_raw::CBOR_Case_Map { v: c· } =>
              raw_uint64 { size: c·.cbor_map_length_size, value: (c·.cbor_map_ptr).len() as u64 },
            cbor_raw::CBOR_Case_Serialized_Map { v: c· } => c·.cbor_serialized_header,
            _ => panic!("Incomplete pattern matching")
        };
    res.value
}

pub(crate) fn cbor_nondet_map_iterator_start <'a>(x: cbor_raw <'a>) ->
    cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
    <'a>
{
    let res: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry = cbor_map_iterator_init(x);
    res
}

pub(crate) fn cbor_nondet_map_iterator_is_empty(
    x: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
) ->
    bool
{ cbor_map_iterator_is_empty(x) }

pub(crate) fn cbor_nondet_map_iterator_next <'b, 'a>(
    x: &'b mut [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>]
) ->
    cbor_map_entry
    <'a>
{ cbor_map_iterator_next(x) }

pub(crate) fn cbor_nondet_map_entry_key <'a>(x2: cbor_map_entry <'a>) -> cbor_raw <'a>
{ x2.cbor_map_entry_key }

pub(crate) fn cbor_nondet_map_entry_value <'a>(x2: cbor_map_entry <'a>) -> cbor_raw <'a>
{ x2.cbor_map_entry_value }

pub(crate) fn cbor_nondet_equal(x1: cbor_raw, x2: cbor_raw) -> bool
{ cbor_nondet_equiv(x1, x2) }

#[derive(PartialEq, Clone, Copy)]
pub enum option__CBOR_Pulse_Raw_Type_cbor_raw <'a>
{
    None,
    Some { v: cbor_raw <'a> }
}

pub(crate) fn cbor_nondet_map_get <'a>(x: cbor_raw <'a>, k: cbor_raw <'a>) ->
    option__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{
    let mut dest: [cbor_raw; 1] = [k; 1usize];
    let i: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
        cbor_nondet_map_iterator_start(x);
    let mut pi: [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry; 1] = [i; 1usize];
    let mut pres: [bool; 1] = [false; 1usize];
    let __anf0: bool = cbor_nondet_map_iterator_is_empty(i);
    let cont: bool = ! __anf0;
    let mut pcont: [bool; 1] = [cont; 1usize];
    let res: bool = (&pres)[0];
    let cont1: bool = (&pcont)[0];
    let mut cond: bool = cont1 && ! res;
    while
    cond
    {
        let y: cbor_map_entry = cbor_nondet_map_iterator_next(&mut pi);
        let __anf01: bool = cbor_nondet_equal(y.cbor_map_entry_key, k);
        if __anf01
        {
            (&mut dest)[0] = y.cbor_map_entry_value;
            (&mut pres)[0] = true
        }
        else
        {
            let i1: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry = (&pi)[0];
            let __anf02: bool = cbor_nondet_map_iterator_is_empty(i1);
            let cont10: bool = ! __anf02;
            (&mut pcont)[0] = cont10
        };
        let res0: bool = (&pres)[0];
        let cont10: bool = (&pcont)[0];
        cond = cont10 && ! res0
    };
    let bres: bool = (&pres)[0];
    if bres
    {
        let res0: cbor_raw = (&dest)[0];
        option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res0 }
    }
    else
    { option__CBOR_Pulse_Raw_Type_cbor_raw::None }
}

pub(crate) fn cbor_nondet_mk_simple_value <'a>(v: u8) -> cbor_raw <'a>
{ cbor_raw::CBOR_Case_Simple { v } }

fn cbor_nondet_mk_int64_gen <'a>(ty: u8, v: u64) -> cbor_raw <'a>
{
    let resi: cbor_int =
        cbor_int
        {
            cbor_int_type: ty,
            cbor_int_size: (mk_raw_uint64(v)).size,
            cbor_int_value: (mk_raw_uint64(v)).value
        };
    cbor_raw::CBOR_Case_Int { v: resi }
}

pub(crate) fn cbor_nondet_mk_uint64 <'a>(v: u64) -> cbor_raw <'a>
{ cbor_nondet_mk_int64_gen(cbor_major_type_uint64, v) }

pub(crate) fn cbor_nondet_mk_neg_int64 <'a>(v: u64) -> cbor_raw <'a>
{ cbor_nondet_mk_int64_gen(cbor_major_type_neg_int64, v) }

pub(crate) fn cbor_nondet_mk_string <'a>(ty: u8, s: &'a [u8]) -> cbor_raw <'a>
{
    let len64: raw_uint64 = mk_raw_uint64(s.len() as u64);
    let ress: cbor_string =
        cbor_string { cbor_string_type: ty, cbor_string_size: len64.size, cbor_string_ptr: s };
    let res1: cbor_raw = cbor_raw::CBOR_Case_String { v: ress };
    cbor_raw_reset_perm_tot(res1)
}

pub(crate) fn cbor_nondet_mk_tagged <'a>(tag: u64, r: &'a [cbor_raw <'a>]) -> cbor_raw <'a>
{
    let tag64: raw_uint64 = mk_raw_uint64(tag);
    let res·: cbor_tagged = cbor_tagged { cbor_tagged_tag: tag64, cbor_tagged_ptr: r };
    let res1: cbor_raw = cbor_raw::CBOR_Case_Tagged { v: res· };
    cbor_raw_reset_perm_tot(res1)
}

pub(crate) fn cbor_nondet_mk_array <'a>(a: &'a [cbor_raw <'a>]) -> cbor_raw <'a>
{
    let len64: raw_uint64 = mk_raw_uint64(a.len() as u64);
    let res·: cbor_array = cbor_array { cbor_array_length_size: len64.size, cbor_array_ptr: a };
    let res1: cbor_raw = cbor_raw::CBOR_Case_Array { v: res· };
    cbor_raw_reset_perm_tot(res1)
}

pub(crate) fn cbor_nondet_mk_map_entry <'a>(xk: cbor_raw <'a>, xv: cbor_raw <'a>) ->
    cbor_map_entry
    <'a>
{
    let xk·: cbor_raw = cbor_raw_reset_perm_tot(xk);
    let xv·: cbor_raw = cbor_raw_reset_perm_tot(xv);
    cbor_map_entry { cbor_map_entry_key: xk·, cbor_map_entry_value: xv· }
}

pub(crate) fn cbor_nondet_mk_map <'a>(a: &'a [cbor_map_entry <'a>]) ->
    option__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{
    let mut dest: [cbor_raw; 1] = [cbor_raw::CBOR_Case_Simple { v: 0u8 }; 1usize];
    let bres: bool =
        if a.len() > 18446744073709551615u64 as usize
        { false }
        else
        {
            let correct: bool = cbor_nondet_no_setoid_repeats(a);
            if correct
            {
                let raw_len: raw_uint64 = mk_raw_uint64(a.len() as u64);
                let res·: cbor_map =
                    cbor_map { cbor_map_length_size: raw_len.size, cbor_map_ptr: a };
                let res1: cbor_raw = cbor_raw::CBOR_Case_Map { v: res· };
                let res: cbor_raw = cbor_raw_reset_perm_tot(res1);
                (&mut dest)[0] = res;
                true
            }
            else
            { false }
        };
    if bres
    {
        let res: cbor_raw = (&dest)[0];
        option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res }
    }
    else
    { option__CBOR_Pulse_Raw_Type_cbor_raw::None }
}

pub const cbor_major_type_simple_value: u8 = 7u8;

pub const cbor_major_type_uint64: u8 = 0u8;

pub const cbor_major_type_neg_int64: u8 = 1u8;

pub const cbor_major_type_byte_string: u8 = 2u8;

pub const cbor_major_type_text_string: u8 = 3u8;

pub const cbor_major_type_array: u8 = 4u8;

pub const cbor_major_type_map: u8 = 5u8;

pub const cbor_major_type_tagged: u8 = 6u8;

pub const min_simple_value_long_argument: u8 = 32u8;

pub const max_simple_value_additional_info: u8 = 23u8;

pub type cbor_array_iterator <'a> = cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>;

pub type cbor_map_iterator <'a> = cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>;

pub type cbor_nondet_t <'a> = cbor_raw <'a>;

pub type cbor_nondet_array_iterator_t <'a> =
cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>;

pub type cbor_nondet_map_iterator_t <'a> =
cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>;

pub type cbor_nondet_map_entry_t <'a> = cbor_map_entry <'a>;
