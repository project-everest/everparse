#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub(crate) const _zero_for_deref: u32 = 0u32;

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
pub struct cbor_raw_serialized_iterator <'a>
{ pub s: &'a [u8], pub len: u64 }

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

pub(crate) fn cbor_mk_map_entry <'a>(xk: cbor_raw <'a>, xv: cbor_raw <'a>) ->
    cbor_map_entry
    <'a>
{
    let res: cbor_map_entry =
        cbor_map_entry
        {
            cbor_map_entry_key: cbor_raw_reset_perm_tot(xk),
            cbor_map_entry_value: cbor_raw_reset_perm_tot(xv)
        };
    res
}

pub(crate) fn mk_raw_uint64(x: u64) -> raw_uint64
{
    let size: u8 =
        if x <= max_simple_value_additional_info as u64
        { 0u8 }
        else if x < 256u64
        { 1u8 }
        else if x < 65536u64 { 2u8 } else if x < 4294967296u64 { 3u8 } else { 4u8 };
    raw_uint64 { size, value: x }
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
    let res0: i16 = (&pres)[0];
    let res1: i16 = res0;
    res1
}

fn read_initial_byte_t(input: &[u8]) -> initial_byte_t
{
    let last: u8 = input[0usize];
    let x: u8 = last;
    let res: initial_byte_t =
        initial_byte_t
        {
            major_type: get_bitfield_gen8(x, 5u32, 8u32),
            additional_info: get_bitfield_gen8(x, 0u32, 5u32)
        };
    let res0: initial_byte_t = res;
    let res1: initial_byte_t = res0;
    let res2: initial_byte_t = res1;
    res2
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
    let res: initial_byte_t = x;
    let x1: initial_byte_t = res;
    let x2: long_argument =
        if x1.additional_info == additional_info_long_argument_8_bits
        {
            if x1.major_type == cbor_major_type_simple_value
            {
                let last: u8 = input2[0usize];
                let x0: u8 = last;
                let res0: long_argument = long_argument::LongArgumentSimpleValue { v: x0 };
                let res1: long_argument = res0;
                let res2: long_argument = res1;
                res2
            }
            else
            {
                let last: u8 = input2[0usize];
                let x0: u8 = last;
                let res0: long_argument = long_argument::LongArgumentU8 { v: x0 };
                let res1: long_argument = res0;
                res1
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
            let res0: long_argument = long_argument::LongArgumentU16 { v: x0 };
            let res1: long_argument = res0;
            res1
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
            let res0: long_argument = long_argument::LongArgumentU32 { v: x0 };
            let res1: long_argument = res0;
            res1
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
            let res0: long_argument = long_argument::LongArgumentU64 { v: x0 };
            let res1: long_argument = res0;
            res1
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
            let res: initial_byte_t = read_initial_byte_t(input·);
            let x: initial_byte_t = res;
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
        let res: initial_byte_t = x;
        let res0: initial_byte_t = res;
        let x0: initial_byte_t = res0;
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
                    let res1: u8 = last;
                    let x1: u8 = res1;
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
    let res: initial_byte_t = x;
    let res0: initial_byte_t = res;
    let x0: initial_byte_t = res0;
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
                    let res0: header = read_header(input·);
                    let x: header = res0;
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
                            let res1: bool =
                                if get_header_major_type(x) == cbor_major_type_byte_string
                                { true }
                                else
                                {
                                    let res1: bool = impl_correct(x1);
                                    res1
                                };
                            res1
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
        let res: header = read_header(input·);
        let x: header = res;
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

fn cbor_validate(input: &[u8]) -> usize
{
    let mut poffset: [usize; 1] = [0usize; 1usize];
    let is_valid: bool = validate_raw_data_item(input, &mut poffset);
    if is_valid { (&poffset)[0] } else { 0usize }
}

fn impl_raw_uint64_optimal(x: raw_uint64) -> bool
{
    if (x.value <= max_simple_value_additional_info as u64) == (x.size == 0u8)
    {
        if x.size <= 1u8
        { true }
        else if x.size == 2u8
        { 256u64 <= x.value }
        else if x.size == 3u8 { 65536u64 <= x.value } else { 4294967296u64 <= x.value }
    }
    else
    { false }
}

fn cbor_raw_ints_optimal(a: &[u8]) -> bool
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
    let _letpattern1: (&[u8], &[u8]) =
        {
            let input1: &[u8] = _letpattern0.0;
            let input2: &[u8] = _letpattern0.1;
            (input1,input2)
        };
    let input1: &[u8] =
        {
            let input1: &[u8] = _letpattern1.0;
            let _input2: &[u8] = _letpattern1.1;
            input1
        };
    let h: header = read_header(input1);
    if get_header_major_type(h) == cbor_major_type_simple_value
    { true }
    else
    {
        impl_raw_uint64_optimal(
            match h.snd
            {
                long_argument::LongArgumentU8 { v } => raw_uint64 { size: 1u8, value: v as u64 },
                long_argument::LongArgumentU16 { v } => raw_uint64 { size: 2u8, value: v as u64 },
                long_argument::LongArgumentU32 { v } => raw_uint64 { size: 3u8, value: v as u64 },
                long_argument::LongArgumentU64 { v } => raw_uint64 { size: 4u8, value: v },
                long_argument::LongArgumentOther =>
                  raw_uint64 { size: 0u8, value: h.fst.additional_info as u64 },
                _ => panic!("Incomplete pattern matching")
            }
        )
    }
}

fn impl_deterministically_encoded_cbor_map_key_order(a1: &[u8], a2: &[u8]) -> bool
{
    let res: i16 = lex_compare_bytes(a1, a2);
    res < 0i16
}

fn cbor_raw_sorted(a: &[u8]) -> bool
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
    let _letpattern1: (&[u8], &[u8]) =
        {
            let input1: &[u8] = _letpattern0.0;
            let input2: &[u8] = _letpattern0.1;
            (input1,input2)
        };
    let input1: &[u8] = _letpattern1.0;
    let input2: &[u8] = _letpattern1.1;
    let h: header = read_header(input1);
    if get_header_major_type(h) == cbor_major_type_map
    {
        let nbpairs: u64 = argument_as_uint64(h.fst, h.snd);
        if nbpairs < 2u64
        { true }
        else
        {
            let b: initial_byte_t = h.fst;
            let i0: usize =
                if
                b.major_type == cbor_major_type_byte_string
                ||
                b.major_type == cbor_major_type_text_string
                {
                    let b0: initial_byte_t = h.fst;
                    let l: long_argument = h.snd;
                    0usize.wrapping_add(argument_as_uint64(b0, l) as usize)
                }
                else
                { 0usize };
            let s0: (&[u8], &[u8]) = input2.split_at(i0);
            let _letpattern10: (&[u8], &[u8]) =
                {
                    let s1: &[u8] = s0.0;
                    let s2: &[u8] = s0.1;
                    (s1,s2)
                };
            let _letpattern11: (&[u8], &[u8]) =
                {
                    let input11: &[u8] = _letpattern10.0;
                    let input21: &[u8] = _letpattern10.1;
                    (input11,input21)
                };
            let _letpattern12: (&[u8], &[u8]) =
                {
                    let input11: &[u8] = _letpattern11.0;
                    let input21: &[u8] = _letpattern11.1;
                    (input11,input21)
                };
            let input3: &[u8] =
                {
                    let _input11: &[u8] = _letpattern12.0;
                    let input21: &[u8] = _letpattern12.1;
                    input21
                };
            let i1: usize = jump_raw_data_item(input3, 0usize);
            let s1: (&[u8], &[u8]) = input3.split_at(i1);
            let _letpattern13: (&[u8], &[u8]) =
                {
                    let s11: &[u8] = s1.0;
                    let s2: &[u8] = s1.1;
                    (s11,s2)
                };
            let _letpattern14: (&[u8], &[u8]) =
                {
                    let input11: &[u8] = _letpattern13.0;
                    let input21: &[u8] = _letpattern13.1;
                    (input11,input21)
                };
            let _letpattern15: (&[u8], &[u8]) =
                {
                    let input11: &[u8] = _letpattern14.0;
                    let input21: &[u8] = _letpattern14.1;
                    (input11,input21)
                };
            let _letpattern16: (&[u8], &[u8]) =
                {
                    let hd: &[u8] = _letpattern15.0;
                    let tl: &[u8] = _letpattern15.1;
                    (hd,tl)
                };
            let hd4: &[u8] = _letpattern16.0;
            let input4: &[u8] = _letpattern16.1;
            let i2: usize = jump_raw_data_item(input4, 0usize);
            let s10: (&[u8], &[u8]) = input4.split_at(i2);
            let _letpattern2: (&[u8], &[u8]) =
                {
                    let s11: &[u8] = s10.0;
                    let s2: &[u8] = s10.1;
                    (s11,s2)
                };
            let _letpattern20: (&[u8], &[u8]) =
                {
                    let input11: &[u8] = _letpattern2.0;
                    let input21: &[u8] = _letpattern2.1;
                    (input11,input21)
                };
            let _letpattern21: (&[u8], &[u8]) =
                {
                    let input11: &[u8] = _letpattern20.0;
                    let input21: &[u8] = _letpattern20.1;
                    (input11,input21)
                };
            let _letpattern22: (&[u8], &[u8]) =
                {
                    let hd: &[u8] = _letpattern21.0;
                    let tl: &[u8] = _letpattern21.1;
                    (hd,tl)
                };
            let input5: &[u8] =
                {
                    let _hd: &[u8] = _letpattern22.0;
                    let tl: &[u8] = _letpattern22.1;
                    tl
                };
            let mut pkey: [&[u8]; 1] = [hd4; 1usize];
            let pairs: u64 = nbpairs.wrapping_sub(1u64);
            let mut ppairs: [u64; 1] = [pairs; 1usize];
            let mut ptail: [&[u8]; 1] = [input5; 1usize];
            let mut pres: [bool; 1] = [true; 1usize];
            let res: bool = (&pres)[0];
            let pairs1: u64 = (&ppairs)[0];
            let mut cond: bool = res && pairs1 > 0u64;
            while
            cond
            {
                let tail: &[u8] = (&ptail)[0];
                let i3: usize = jump_raw_data_item(tail, 0usize);
                let s11: (&[u8], &[u8]) = tail.split_at(i3);
                let _letpattern23: (&[u8], &[u8]) =
                    {
                        let s110: &[u8] = s11.0;
                        let s2: &[u8] = s11.1;
                        (s110,s2)
                    };
                let _letpattern24: (&[u8], &[u8]) =
                    {
                        let input11: &[u8] = _letpattern23.0;
                        let input21: &[u8] = _letpattern23.1;
                        (input11,input21)
                    };
                let _letpattern25: (&[u8], &[u8]) =
                    {
                        let input11: &[u8] = _letpattern24.0;
                        let input21: &[u8] = _letpattern24.1;
                        (input11,input21)
                    };
                let _letpattern26: (&[u8], &[u8]) =
                    {
                        let hd: &[u8] = _letpattern25.0;
                        let tl: &[u8] = _letpattern25.1;
                        (hd,tl)
                    };
                {
                    let key2: &[u8] = _letpattern26.0;
                    let tail2: &[u8] = _letpattern26.1;
                    let key1: &[u8] = (&pkey)[0];
                    let res0: bool = impl_deterministically_encoded_cbor_map_key_order(key1, key2);
                    if res0
                    {
                        let i4: usize = jump_raw_data_item(tail2, 0usize);
                        let s12: (&[u8], &[u8]) = tail2.split_at(i4);
                        let _letpattern3: (&[u8], &[u8]) =
                            {
                                let s110: &[u8] = s12.0;
                                let s2: &[u8] = s12.1;
                                (s110,s2)
                            };
                        let _letpattern30: (&[u8], &[u8]) =
                            {
                                let input11: &[u8] = _letpattern3.0;
                                let input21: &[u8] = _letpattern3.1;
                                (input11,input21)
                            };
                        let _letpattern31: (&[u8], &[u8]) =
                            {
                                let input11: &[u8] = _letpattern30.0;
                                let input21: &[u8] = _letpattern30.1;
                                (input11,input21)
                            };
                        let _letpattern32: (&[u8], &[u8]) =
                            {
                                let hd: &[u8] = _letpattern31.0;
                                let tl: &[u8] = _letpattern31.1;
                                (hd,tl)
                            };
                        let tail·: &[u8] =
                            {
                                let _hd: &[u8] = _letpattern32.0;
                                let tl: &[u8] = _letpattern32.1;
                                tl
                            };
                        (&mut pkey)[0] = key2;
                        let pairs10: u64 = (&ppairs)[0];
                        let pairs·: u64 = pairs10.wrapping_sub(1u64);
                        (&mut ppairs)[0] = pairs·;
                        (&mut ptail)[0] = tail·
                    }
                    else
                    { (&mut pres)[0] = false }
                };
                let res0: bool = (&pres)[0];
                let pairs10: u64 = (&ppairs)[0];
                cond = res0 && pairs10 > 0u64
            };
            (&pres)[0]
        }
    }
    else
    { true }
}

fn cbor_validate_det·(input: &[u8]) -> usize
{
    let len: usize = cbor_validate(input);
    if len == 0usize
    { len }
    else
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
        let check: [bool; 1] = [false; 1usize];
        crate::lowstar::ignore::ignore::<&[bool]>(&check);
        let mut pn: [usize; 1] = [1usize; 1usize];
        let mut pres: [bool; 1] = [true; 1usize];
        let mut ppi: [&[u8]; 1] = [input1; 1usize];
        let res: bool = (&pres)[0];
        let n: usize = (&pn)[0];
        let mut cond: bool = res && n > 0usize;
        while
        cond
        {
            let n0: usize = (&pn)[0];
            let pi: &[u8] = (&ppi)[0];
            let res0: bool = cbor_raw_ints_optimal(pi);
            if ! res0
            { (&mut pres)[0] = false }
            else
            {
                let off1: usize = jump_header(pi, 0usize);
                let s·0: (&[u8], &[u8]) = pi.split_at(0usize);
                let _letpattern0: (&[u8], &[u8]) =
                    {
                        let s1: &[u8] = s·0.0;
                        let s2: &[u8] = s·0.1;
                        (s1,s2)
                    };
                let input·: &[u8] =
                    {
                        let _input11: &[u8] = _letpattern0.0;
                        let input23: &[u8] = _letpattern0.1;
                        let consumed: usize = off1.wrapping_sub(0usize);
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
                let res1: header = read_header(input·);
                let x: header = res1;
                let b: initial_byte_t = x.fst;
                let i: usize =
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
                let s: (&[u8], &[u8]) = pi.split_at(i);
                let _letpattern1: (&[u8], &[u8]) =
                    {
                        let s1: &[u8] = s.0;
                        let s2: &[u8] = s.1;
                        (s1,s2)
                    };
                let _letpattern2: (&[u8], &[u8]) =
                    {
                        let input11: &[u8] = _letpattern1.0;
                        let input2: &[u8] = _letpattern1.1;
                        (input11,input2)
                    };
                let ph: &[u8] = _letpattern2.0;
                let pc: &[u8] = _letpattern2.1;
                let unused: usize = pc.len();
                crate::lowstar::ignore::ignore::<usize>(unused);
                let count: usize = jump_recursive_step_count_leaf(ph);
                (&mut pn)[0] = n0.wrapping_sub(1usize).wrapping_add(count);
                (&mut ppi)[0] = pc
            };
            let res1: bool = (&pres)[0];
            let n1: usize = (&pn)[0];
            cond = res1 && n1 > 0usize
        };
        let res0: bool = (&pres)[0];
        let check1: bool = res0;
        if ! check1
        { 0usize }
        else
        {
            let mut pn0: [usize; 1] = [1usize; 1usize];
            let mut pres0: [bool; 1] = [true; 1usize];
            let mut ppi0: [&[u8]; 1] = [input1; 1usize];
            let res1: bool = (&pres0)[0];
            let n0: usize = (&pn0)[0];
            let mut cond0: bool = res1 && n0 > 0usize;
            while
            cond0
            {
                let n1: usize = (&pn0)[0];
                let pi: &[u8] = (&ppi0)[0];
                let res2: bool = cbor_raw_sorted(pi);
                if ! res2
                { (&mut pres0)[0] = false }
                else
                {
                    let off1: usize = jump_header(pi, 0usize);
                    let s·0: (&[u8], &[u8]) = pi.split_at(0usize);
                    let _letpattern0: (&[u8], &[u8]) =
                        {
                            let s1: &[u8] = s·0.0;
                            let s2: &[u8] = s·0.1;
                            (s1,s2)
                        };
                    let input·: &[u8] =
                        {
                            let _input11: &[u8] = _letpattern0.0;
                            let input23: &[u8] = _letpattern0.1;
                            let consumed: usize = off1.wrapping_sub(0usize);
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
                    let res10: header = read_header(input·);
                    let x: header = res10;
                    let b: initial_byte_t = x.fst;
                    let i: usize =
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
                    let s: (&[u8], &[u8]) = pi.split_at(i);
                    let _letpattern1: (&[u8], &[u8]) =
                        {
                            let s1: &[u8] = s.0;
                            let s2: &[u8] = s.1;
                            (s1,s2)
                        };
                    let _letpattern2: (&[u8], &[u8]) =
                        {
                            let input11: &[u8] = _letpattern1.0;
                            let input2: &[u8] = _letpattern1.1;
                            (input11,input2)
                        };
                    let ph: &[u8] = _letpattern2.0;
                    let pc: &[u8] = _letpattern2.1;
                    let unused: usize = pc.len();
                    crate::lowstar::ignore::ignore::<usize>(unused);
                    let count: usize = jump_recursive_step_count_leaf(ph);
                    (&mut pn0)[0] = n1.wrapping_sub(1usize).wrapping_add(count);
                    (&mut ppi0)[0] = pc
                };
                let res3: bool = (&pres0)[0];
                let n2: usize = (&pn0)[0];
                cond0 = res3 && n2 > 0usize
            };
            let res2: bool = (&pres0)[0];
            let check2: bool = res2;
            if ! check2 { 0usize } else { len }
        }
    }
}

pub(crate) fn cbor_validate_det(input: &[u8]) -> usize { cbor_validate_det·(input) }

pub(crate) fn cbor_parse <'a>(input: &'a [u8], len: usize) -> cbor_raw <'a>
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
    let res: cbor_raw = cbor_read(input1);
    res
}

fn cbor_jump(input: &[u8], off: usize) -> usize { jump_raw_data_item(input, off) }

#[derive(PartialEq, Clone, Copy)]
enum cbor_raw_map_insert_result
{
    CFailure,
    CInProgress,
    CSuccess
}

fn uu___is_CInProgress(projectee: cbor_raw_map_insert_result) -> bool
{ match projectee { cbor_raw_map_insert_result::CInProgress => true, _ => false } }

pub(crate) fn cbor_raw_map_insert(out: &mut [u8], off2: usize, off3: usize) -> bool
{
    let mut poff: [usize; 1] = [0usize; 1usize];
    let mut pres: [cbor_raw_map_insert_result; 1] =
        [cbor_raw_map_insert_result::CInProgress; 1usize];
    let res: cbor_raw_map_insert_result = (&pres)[0];
    let mut cond: bool =
        if uu___is_CInProgress(res)
        {
            let off: usize = (&poff)[0];
            off < off2
        }
        else
        { false };
    while
    cond
    {
        let off: usize = (&poff)[0];
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(off);
        {
            let _out1: &[u8] = _letpattern.0;
            let out2kv: &mut [u8] = _letpattern.1;
            let _letpattern1: (&[u8], &[u8]) = out2kv.split_at(off2.wrapping_sub(off));
            let out2: &[u8] = _letpattern1.0;
            let outkv: &[u8] = _letpattern1.1;
            let _letpattern2: (&[u8], &[u8]) = outkv.split_at(off3.wrapping_sub(off2));
            let outk: &[u8] = _letpattern2.0;
            let _outv: &[u8] = _letpattern2.1;
            let offk: usize = cbor_jump(out2, 0usize);
            let _letpattern3: (&[u8], &[u8]) = out2.split_at(offk);
            let outk·: &[u8] = _letpattern3.0;
            let outvq: &[u8] = _letpattern3.1;
            let c: i16 = lex_compare_bytes(outk·, outk);
            if c < 0i16
            {
                let offq: usize = cbor_jump(outvq, 0usize);
                let off·: usize = off.wrapping_add(offk.wrapping_add(offq));
                (&mut poff)[0] = off·
            }
            else if c > 0i16
            {
                if ! (off2.wrapping_sub(off) == 0usize || off2.wrapping_sub(off) == out2kv.len())
                {
                    let mut pn: [usize; 1] = [out2kv.len(); 1usize];
                    let mut pl: [usize; 1] = [off2.wrapping_sub(off); 1usize];
                    let __anf0: usize = (&pl)[0];
                    let mut cond0: bool = __anf0 > 0usize;
                    while
                    cond0
                    {
                        let n: usize = (&pn)[0];
                        let l: usize = (&pl)[0];
                        let l·: usize = n.wrapping_rem(l);
                        (&mut pn)[0] = l;
                        (&mut pl)[0] = l·;
                        let __anf00: usize = (&pl)[0];
                        cond0 = __anf00 > 0usize
                    };
                    let d: usize = (&pn)[0];
                    let q: usize = out2kv.len().wrapping_div(d);
                    let mut pi: [usize; 1] = [0usize; 1usize];
                    let __anf00: usize = (&pi)[0];
                    let mut cond1: bool = __anf00 < d;
                    while
                    cond1
                    {
                        let i: usize = (&pi)[0];
                        let save: u8 = out2kv[i];
                        let mut pj: [usize; 1] = [0usize; 1usize];
                        let mut pidx: [usize; 1] = [i; 1usize];
                        let __anf01: usize = (&pj)[0];
                        let mut cond2: bool = __anf01 < q.wrapping_sub(1usize);
                        while
                        cond2
                        {
                            let j: usize = (&pj)[0];
                            let idx: usize = (&pidx)[0];
                            let idx·: usize =
                                if
                                idx.wrapping_sub(0usize)
                                >=
                                out2kv.len().wrapping_sub(off2.wrapping_sub(off))
                                {
                                    idx.wrapping_sub(
                                        out2kv.len().wrapping_sub(off2.wrapping_sub(off))
                                    )
                                }
                                else
                                { idx.wrapping_add(off2.wrapping_sub(off).wrapping_sub(0usize)) };
                            let x: u8 = out2kv[idx·];
                            let j·: usize = j.wrapping_add(1usize);
                            out2kv[idx] = x;
                            (&mut pj)[0] = j·;
                            (&mut pidx)[0] = idx·;
                            let __anf02: usize = (&pj)[0];
                            cond2 = __anf02 < q.wrapping_sub(1usize)
                        };
                        let idx: usize = (&pidx)[0];
                        out2kv[idx] = save;
                        let i·: usize = i.wrapping_add(1usize);
                        (&mut pi)[0] = i·;
                        let __anf02: usize = (&pi)[0];
                        cond1 = __anf02 < d
                    }
                };
                (&mut pres)[0] = cbor_raw_map_insert_result::CSuccess
            }
            else
            { (&mut pres)[0] = cbor_raw_map_insert_result::CFailure }
        };
        let res0: cbor_raw_map_insert_result = (&pres)[0];
        let ite: bool =
            if uu___is_CInProgress(res0)
            {
                let off0: usize = (&poff)[0];
                off0 < off2
            }
            else
            { false };
        cond = ite
    };
    let res0: cbor_raw_map_insert_result = (&pres)[0];
    match res0
    {
        cbor_raw_map_insert_result::CSuccess => true,
        cbor_raw_map_insert_result::CFailure => false,
        cbor_raw_map_insert_result::CInProgress => true,
        _ => panic!("Precondition of the function most likely violated")
    }
}

fn cbor_match_serialized_tagged_get_payload <'a>(c: cbor_serialized <'a>) -> cbor_raw <'a>
{
    let res: cbor_raw = cbor_read(c.cbor_serialized_payload);
    res
}

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
        let res1: &[u8] =
            {
                let _input1: &[u8] = _letpattern1.0;
                let input2: &[u8] = _letpattern1.1;
                input2
            };
        let res2: &[u8] = res1;
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
    let res1: &[u8] =
        {
            let input1: &[u8] = _letpattern1.0;
            let _input2: &[u8] = _letpattern1.1;
            input1
        };
    let res2: &[u8] = res1;
    let elt: &[u8] = res2;
    let res0: cbor_raw = cbor_read(elt);
    res0
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

pub(crate) fn cbor_match_tagged_get_payload <'a>(c: cbor_raw <'a>) -> cbor_raw <'a>
{
    match c
    {
        cbor_raw::CBOR_Case_Serialized_Tagged { v: cs } =>
          {
              let res: cbor_raw = cbor_match_serialized_tagged_get_payload(cs);
              res
          },
        cbor_raw::CBOR_Case_Tagged { v: ct } => ct.cbor_tagged_ptr[0],
        _ => panic!("Incomplete pattern matching")
    }
}

pub(crate) fn cbor_array_item <'a>(c: cbor_raw <'a>, i: u64) -> cbor_raw <'a>
{
    match c
    {
        cbor_raw::CBOR_Case_Serialized_Array { v: c· } =>
          {
              let res: cbor_raw = cbor_serialized_array_item(c·, i);
              res
          },
        cbor_raw::CBOR_Case_Array { v: c· } =>
          {
              let res: cbor_raw = c·.cbor_array_ptr[i as usize];
              res
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub(crate) fn cbor_array_iterator_init <'a>(c: cbor_raw <'a>) ->
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

pub(crate) fn cbor_array_iterator_is_empty(c: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw) ->
    bool
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

pub(crate) fn cbor_array_iterator_next <'b, 'a>(
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
              let res0: cbor_raw = res;
              res0
          },
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized { _0: i1 } =>
          {
              let res: cbor_raw = cbor_serialized_array_iterator_next(pi, i1);
              res
          },
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

pub(crate) fn cbor_map_iterator_init <'a>(c: cbor_raw <'a>) ->
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

pub(crate) fn cbor_map_iterator_is_empty(
    c: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
) ->
    bool
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

pub(crate) fn cbor_map_iterator_next <'b, 'a>(
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
              let res0: cbor_map_entry = res;
              res0
          },
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
        { _0: i1 }
        =>
          {
              let res: cbor_map_entry = cbor_serialized_map_iterator_next(pi, i1);
              res
          },
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
    let res: usize =
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
        { res1 };
    let res2: usize = res;
    res2
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
        let res: bool =
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
            { true };
        let res2: bool = res;
        res2
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
option__LowParse_Pulse_Base_with_perm·Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_tags
{
    None,
    Some
}

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
    let res2: usize =
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
            let _letpattern0: (&mut [u8], &mut [u8]) = out.split_at_mut(res1);
            let res: usize =
                {
                    let _sp11: &[u8] = _letpattern0.0;
                    let sp12: &mut [u8] = _letpattern0.1;
                    let _letpattern1: (&mut [u8], &mut [u8]) = sp12.split_at_mut(length);
                    let sp21: &mut [u8] = _letpattern1.0;
                    let _sp22: &[u8] = _letpattern1.1;
                    sp21.copy_from_slice(x2·);
                    res1.wrapping_add(length)
                };
            res
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
                        let res0: usize = res;
                        (&mut pi)[0] = i·;
                        (&mut pres)[0] = res0;
                        let i1: usize = (&pi)[0];
                        cond = i1 < argument_as_uint64(xh1.fst, xh1.snd) as usize
                    };
                    let res: usize = (&pres)[0];
                    res
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
                    let _letpattern0: (&mut [u8], &mut [u8]) = out.split_at_mut(res1);
                    let res: usize =
                        {
                            let _sp11: &[u8] = _letpattern0.0;
                            let sp12: &mut [u8] = _letpattern0.1;
                            let _letpattern1: (&mut [u8], &mut [u8]) = sp12.split_at_mut(length);
                            let sp21: &mut [u8] = _letpattern1.0;
                            let _sp22: &[u8] = _letpattern1.1;
                            sp21.copy_from_slice(x2·);
                            res1.wrapping_add(length)
                        };
                    res
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
                            let res2: usize = ser·(x2, out, res11);
                            let res: usize = res2;
                            (&mut pi)[0] = i·;
                            (&mut pres)[0] = res;
                            let i1: usize = (&pi)[0];
                            cond = i1 < argument_as_uint64(xh1.fst, xh1.snd) as usize
                        };
                        let res: usize = (&pres)[0];
                        res
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
                        let res: usize =
                            {
                                let _sp11: &[u8] = _letpattern0.0;
                                let sp12: &mut [u8] = _letpattern0.1;
                                let _letpattern1: (&mut [u8], &mut [u8]) =
                                    sp12.split_at_mut(length);
                                let sp21: &mut [u8] = _letpattern1.0;
                                let _sp22: &[u8] = _letpattern1.1;
                                sp21.copy_from_slice(x2·);
                                res1.wrapping_add(length)
                            };
                        res
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
                            let res: usize = ser·(x2·, out, res1);
                            res
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
                            let res: usize =
                                {
                                    let _sp11: &[u8] = _letpattern0.0;
                                    let sp12: &mut [u8] = _letpattern0.1;
                                    let _letpattern1: (&mut [u8], &mut [u8]) =
                                        sp12.split_at_mut(length);
                                    let sp21: &mut [u8] = _letpattern1.0;
                                    let _sp22: &[u8] = _letpattern1.1;
                                    sp21.copy_from_slice(x2·);
                                    res1.wrapping_add(length)
                                };
                            res
                        }
                    }
                    else
                    { res1 }
                }
            }
        };
    let res: usize = res2;
    res
}

fn ser(x1·: cbor_raw, out: &mut [u8], offset: usize) -> usize
{
    let x2·: cbor_raw = x1·;
    let res: usize = ser·(x2·, out, offset);
    res
}

pub(crate) fn cbor_serialize(x: cbor_raw, output: &mut [u8]) -> usize
{ ser(x, output, 0usize) }

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
                        let res2: bool = res0;
                        if res2
                        {
                            let i·: usize = i0.wrapping_add(1usize);
                            (&mut pi)[0] = i·
                        }
                        else
                        { (&mut pres)[0] = false };
                        let res3: bool = (&pres)[0];
                        let i1: usize = (&pi)[0];
                        cond = res3 && i1 < argument_as_uint64(xh1.fst, xh1.snd) as usize
                    };
                    let res0: bool = (&pres)[0];
                    res0
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
                                    let res2: bool = siz·(x2, out);
                                    res2
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
                        let res0: bool = (&pres)[0];
                        res0
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
                            let res: bool = siz·(x2·, out);
                            res
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
    let res: bool = siz·(x2·, out);
    res
}

pub(crate) fn cbor_size(x: cbor_raw, bound: usize) -> usize
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

pub(crate) fn cbor_serialize_tag(tag: raw_uint64, output: &mut [u8]) -> usize
{
    let h: header = raw_uint64_as_argument(cbor_major_type_tagged, tag);
    let mut slen: [usize; 1] = [output.len(); 1usize];
    let fits: bool = size_header(h, &mut slen);
    if fits
    {
        let res: usize = write_header(h, output, 0usize);
        res
    }
    else
    { 0usize }
}

fn cbor_serialize_array·(len: raw_uint64, out: &mut [u8], off: usize) -> usize
{
    let slen: usize = out.len();
    let mut rem: [usize; 1] = [slen.wrapping_sub(off); 1usize];
    let h: header = raw_uint64_as_argument(cbor_major_type_array, len);
    let hfits: bool = size_header(h, &mut rem);
    if hfits
    {
        let llen: usize = write_header(h, out, off);
        let sp: (&mut [u8], &mut [u8]) = out.split_at_mut(llen);
        let sp1: &mut [u8] = sp.0;
        let _sp2: &[u8] = sp.1;
        if ! (off == 0usize || off == sp1.len())
        {
            let mut pn: [usize; 1] = [sp1.len(); 1usize];
            let mut pl: [usize; 1] = [off; 1usize];
            let __anf0: usize = (&pl)[0];
            let mut cond: bool = __anf0 > 0usize;
            while
            cond
            {
                let n: usize = (&pn)[0];
                let l1: usize = (&pl)[0];
                let l·: usize = n.wrapping_rem(l1);
                (&mut pn)[0] = l1;
                (&mut pl)[0] = l·;
                let __anf00: usize = (&pl)[0];
                cond = __anf00 > 0usize
            };
            let d: usize = (&pn)[0];
            let q: usize = sp1.len().wrapping_div(d);
            let mut pi: [usize; 1] = [0usize; 1usize];
            let __anf00: usize = (&pi)[0];
            let mut cond0: bool = __anf00 < d;
            while
            cond0
            {
                let i: usize = (&pi)[0];
                let save: u8 = sp1[i];
                let mut pj: [usize; 1] = [0usize; 1usize];
                let mut pidx: [usize; 1] = [i; 1usize];
                let __anf01: usize = (&pj)[0];
                let mut cond1: bool = __anf01 < q.wrapping_sub(1usize);
                while
                cond1
                {
                    let j: usize = (&pj)[0];
                    let idx: usize = (&pidx)[0];
                    let idx·: usize =
                        if idx.wrapping_sub(0usize) >= sp1.len().wrapping_sub(off)
                        { idx.wrapping_sub(sp1.len().wrapping_sub(off)) }
                        else
                        { idx.wrapping_add(off.wrapping_sub(0usize)) };
                    let x: u8 = sp1[idx·];
                    let j·: usize = j.wrapping_add(1usize);
                    sp1[idx] = x;
                    (&mut pj)[0] = j·;
                    (&mut pidx)[0] = idx·;
                    let __anf02: usize = (&pj)[0];
                    cond1 = __anf02 < q.wrapping_sub(1usize)
                };
                let idx: usize = (&pidx)[0];
                sp1[idx] = save;
                let i·: usize = i.wrapping_add(1usize);
                (&mut pi)[0] = i·;
                let __anf02: usize = (&pi)[0];
                cond0 = __anf02 < d
            }
        };
        llen
    }
    else
    { 0usize }
}

pub(crate) fn cbor_serialize_array(len: raw_uint64, out: &mut [u8], off: usize) -> usize
{ cbor_serialize_array·(len, out, off) }

pub(crate) fn cbor_serialize_string(ty: u8, off: raw_uint64, out: &mut [u8]) -> usize
{
    let soff: usize = off.value as usize;
    let slen: usize = out.len();
    let mut rem: [usize; 1] = [slen.wrapping_sub(soff); 1usize];
    let h: header = raw_uint64_as_argument(ty, off);
    let hfits: bool = size_header(h, &mut rem);
    if hfits
    {
        let llen: usize = write_header(h, out, soff);
        let sp: (&mut [u8], &mut [u8]) = out.split_at_mut(llen);
        let sp1: &mut [u8] = sp.0;
        let _sp2: &[u8] = sp.1;
        if ! (soff == 0usize || soff == sp1.len())
        {
            let mut pn: [usize; 1] = [sp1.len(); 1usize];
            let mut pl: [usize; 1] = [soff; 1usize];
            let __anf0: usize = (&pl)[0];
            let mut cond: bool = __anf0 > 0usize;
            while
            cond
            {
                let n: usize = (&pn)[0];
                let l: usize = (&pl)[0];
                let l·: usize = n.wrapping_rem(l);
                (&mut pn)[0] = l;
                (&mut pl)[0] = l·;
                let __anf00: usize = (&pl)[0];
                cond = __anf00 > 0usize
            };
            let d: usize = (&pn)[0];
            let q: usize = sp1.len().wrapping_div(d);
            let mut pi: [usize; 1] = [0usize; 1usize];
            let __anf00: usize = (&pi)[0];
            let mut cond0: bool = __anf00 < d;
            while
            cond0
            {
                let i: usize = (&pi)[0];
                let save: u8 = sp1[i];
                let mut pj: [usize; 1] = [0usize; 1usize];
                let mut pidx: [usize; 1] = [i; 1usize];
                let __anf01: usize = (&pj)[0];
                let mut cond1: bool = __anf01 < q.wrapping_sub(1usize);
                while
                cond1
                {
                    let j: usize = (&pj)[0];
                    let idx: usize = (&pidx)[0];
                    let idx·: usize =
                        if idx.wrapping_sub(0usize) >= sp1.len().wrapping_sub(soff)
                        { idx.wrapping_sub(sp1.len().wrapping_sub(soff)) }
                        else
                        { idx.wrapping_add(soff.wrapping_sub(0usize)) };
                    let x: u8 = sp1[idx·];
                    let j·: usize = j.wrapping_add(1usize);
                    sp1[idx] = x;
                    (&mut pj)[0] = j·;
                    (&mut pidx)[0] = idx·;
                    let __anf02: usize = (&pj)[0];
                    cond1 = __anf02 < q.wrapping_sub(1usize)
                };
                let idx: usize = (&pidx)[0];
                sp1[idx] = save;
                let i·: usize = i.wrapping_add(1usize);
                (&mut pi)[0] = i·;
                let __anf02: usize = (&pi)[0];
                cond0 = __anf02 < d
            }
        };
        llen
    }
    else
    { 0usize }
}

fn cbor_serialize_map·(len: raw_uint64, out: &mut [u8], off: usize) -> usize
{
    let slen: usize = out.len();
    let mut rem: [usize; 1] = [slen.wrapping_sub(off); 1usize];
    let h: header = raw_uint64_as_argument(cbor_major_type_map, len);
    let hfits: bool = size_header(h, &mut rem);
    if hfits
    {
        let llen: usize = write_header(h, out, off);
        let sp: (&mut [u8], &mut [u8]) = out.split_at_mut(llen);
        let sp1: &mut [u8] = sp.0;
        let _sp2: &[u8] = sp.1;
        if ! (off == 0usize || off == sp1.len())
        {
            let mut pn: [usize; 1] = [sp1.len(); 1usize];
            let mut pl: [usize; 1] = [off; 1usize];
            let __anf0: usize = (&pl)[0];
            let mut cond: bool = __anf0 > 0usize;
            while
            cond
            {
                let n: usize = (&pn)[0];
                let l1: usize = (&pl)[0];
                let l·: usize = n.wrapping_rem(l1);
                (&mut pn)[0] = l1;
                (&mut pl)[0] = l·;
                let __anf00: usize = (&pl)[0];
                cond = __anf00 > 0usize
            };
            let d: usize = (&pn)[0];
            let q: usize = sp1.len().wrapping_div(d);
            let mut pi: [usize; 1] = [0usize; 1usize];
            let __anf00: usize = (&pi)[0];
            let mut cond0: bool = __anf00 < d;
            while
            cond0
            {
                let i: usize = (&pi)[0];
                let save: u8 = sp1[i];
                let mut pj: [usize; 1] = [0usize; 1usize];
                let mut pidx: [usize; 1] = [i; 1usize];
                let __anf01: usize = (&pj)[0];
                let mut cond1: bool = __anf01 < q.wrapping_sub(1usize);
                while
                cond1
                {
                    let j: usize = (&pj)[0];
                    let idx: usize = (&pidx)[0];
                    let idx·: usize =
                        if idx.wrapping_sub(0usize) >= sp1.len().wrapping_sub(off)
                        { idx.wrapping_sub(sp1.len().wrapping_sub(off)) }
                        else
                        { idx.wrapping_add(off.wrapping_sub(0usize)) };
                    let x: u8 = sp1[idx·];
                    let j·: usize = j.wrapping_add(1usize);
                    sp1[idx] = x;
                    (&mut pj)[0] = j·;
                    (&mut pidx)[0] = idx·;
                    let __anf02: usize = (&pj)[0];
                    cond1 = __anf02 < q.wrapping_sub(1usize)
                };
                let idx: usize = (&pidx)[0];
                sp1[idx] = save;
                let i·: usize = i.wrapping_add(1usize);
                (&mut pi)[0] = i·;
                let __anf02: usize = (&pi)[0];
                cond0 = __anf02 < d
            }
        };
        llen
    }
    else
    { 0usize }
}

pub(crate) fn cbor_serialize_map(len: raw_uint64, out: &mut [u8], off: usize) -> usize
{ cbor_serialize_map·(len, out, off) }

fn cbor_match_compare_serialized_tagged(c1: cbor_serialized, c2: cbor_serialized) -> i16
{ lex_compare_bytes(c1.cbor_serialized_payload, c2.cbor_serialized_payload) }

fn cbor_match_compare_serialized_array(c1: cbor_serialized, c2: cbor_serialized) -> i16
{ lex_compare_bytes(c1.cbor_serialized_payload, c2.cbor_serialized_payload) }

fn cbor_match_compare_serialized_map(c1: cbor_serialized, c2: cbor_serialized) -> i16
{ lex_compare_bytes(c1.cbor_serialized_payload, c2.cbor_serialized_payload) }

pub(crate) fn impl_major_type(x: cbor_raw) -> u8
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

fn uint64_compare(x1: u64, x2: u64) -> i16
{ if x1 < x2 { -1i16 } else if x1 > x2 { 1i16 } else { 0i16 } }

fn impl_raw_uint64_compare(x1: raw_uint64, x2: raw_uint64) -> i16
{
    let c: i16 = impl_uint8_compare(x1.size, x2.size);
    if c == 0i16 { uint64_compare(x1.value, x2.value) } else { c }
}

#[derive(PartialEq, Clone, Copy)]
enum
option__·CBOR_Pulse_Raw_Type_cbor_serialized···CBOR_Pulse_Raw_Type_cbor_serialized·
<'a>
{
    None,
    Some { v: (cbor_serialized <'a>, cbor_serialized <'a>) }
}

fn cbor_pair_is_serialized <'a>(c1: cbor_raw <'a>, c2: cbor_raw <'a>) ->
    option__·CBOR_Pulse_Raw_Type_cbor_serialized···CBOR_Pulse_Raw_Type_cbor_serialized·
    <'a>
{
    match c1
    {
        cbor_raw::CBOR_Case_Serialized_Tagged { v: s1 } =>
          match c2
          {
              cbor_raw::CBOR_Case_Serialized_Tagged { v: s2 } =>
                option__·CBOR_Pulse_Raw_Type_cbor_serialized···CBOR_Pulse_Raw_Type_cbor_serialized·::Some
                { v: (s1,s2) },
              _ =>
                option__·CBOR_Pulse_Raw_Type_cbor_serialized···CBOR_Pulse_Raw_Type_cbor_serialized·::None
          },
        _ =>
          option__·CBOR_Pulse_Raw_Type_cbor_serialized···CBOR_Pulse_Raw_Type_cbor_serialized·::None
    }
}

fn fst__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized <'a>(
    x: (cbor_serialized <'a>, cbor_serialized <'a>)
) ->
    cbor_serialized
    <'a>
{
    let _1: cbor_serialized = x.0;
    let __2: cbor_serialized = x.1;
    _1
}

fn snd__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized <'a>(
    x: (cbor_serialized <'a>, cbor_serialized <'a>)
) ->
    cbor_serialized
    <'a>
{
    let __1: cbor_serialized = x.0;
    let _2: cbor_serialized = x.1;
    _2
}

pub(crate) fn impl_cbor_compare(x1: cbor_raw, x2: cbor_raw) -> i16
{
    let ty1: u8 = impl_major_type(x1);
    let ty2: u8 = impl_major_type(x2);
    let c: i16 = impl_uint8_compare(ty1, ty2);
    if c == 0i16
    {
        if ty1 == cbor_major_type_uint64 || ty1 == cbor_major_type_neg_int64
        {
            let _letpattern: cbor_raw = x1;
            let i1: raw_uint64 =
                match _letpattern
                {
                    cbor_raw::CBOR_Case_Int { v: c· } =>
                      raw_uint64 { size: c·.cbor_int_size, value: c·.cbor_int_value },
                    _ => panic!("Incomplete pattern matching")
                };
            let _letpattern0: cbor_raw = x2;
            let i2: raw_uint64 =
                match _letpattern0
                {
                    cbor_raw::CBOR_Case_Int { v: c· } =>
                      raw_uint64 { size: c·.cbor_int_size, value: c·.cbor_int_value },
                    _ => panic!("Incomplete pattern matching")
                };
            impl_raw_uint64_compare(i1, i2)
        }
        else if ty1 == cbor_major_type_byte_string || ty1 == cbor_major_type_text_string
        {
            let _letpattern: cbor_raw = x1;
            let i1: raw_uint64 =
                match _letpattern
                {
                    cbor_raw::CBOR_Case_String { v: c· } =>
                      raw_uint64
                      { size: c·.cbor_string_size, value: (c·.cbor_string_ptr).len() as u64 },
                    _ => panic!("Incomplete pattern matching")
                };
            let _letpattern0: cbor_raw = x2;
            let i2: raw_uint64 =
                match _letpattern0
                {
                    cbor_raw::CBOR_Case_String { v: c· } =>
                      raw_uint64
                      { size: c·.cbor_string_size, value: (c·.cbor_string_ptr).len() as u64 },
                    _ => panic!("Incomplete pattern matching")
                };
            let c1: i16 = impl_raw_uint64_compare(i1, i2);
            if c1 == 0i16
            {
                let _letpattern1: cbor_raw = x1;
                let pl1: &[u8] =
                    match _letpattern1
                    {
                        cbor_raw::CBOR_Case_String { v: c· } => c·.cbor_string_ptr,
                        _ => panic!("Incomplete pattern matching")
                    };
                let _letpattern2: cbor_raw = x2;
                let pl2: &[u8] =
                    match _letpattern2
                    {
                        cbor_raw::CBOR_Case_String { v: c· } => c·.cbor_string_ptr,
                        _ => panic!("Incomplete pattern matching")
                    };
                let res: i16 = lex_compare_bytes(pl1, pl2);
                res
            }
            else
            { c1 }
        }
        else if ty1 == cbor_major_type_tagged
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
            let c1: i16 = impl_raw_uint64_compare(tag1, tag2);
            if c1 == 0i16
            {
                match cbor_pair_is_serialized(x1, x2)
                {
                    option__·CBOR_Pulse_Raw_Type_cbor_serialized···CBOR_Pulse_Raw_Type_cbor_serialized·::Some
                    { v: pair }
                    =>
                      {
                          let res: i16 =
                              cbor_match_compare_serialized_tagged(
                                  fst__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized(
                                      pair
                                  ),
                                  snd__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized(
                                      pair
                                  )
                              );
                          res
                      },
                    _ =>
                      {
                          let pl1: cbor_raw = cbor_match_tagged_get_payload(x1);
                          let pl2: cbor_raw = cbor_match_tagged_get_payload(x2);
                          let res: i16 = impl_cbor_compare(pl1, pl2);
                          res
                      }
                }
            }
            else
            { c1 }
        }
        else if ty1 == cbor_major_type_array
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
            let c1: i16 = impl_raw_uint64_compare(len1, len2);
            if c1 == 0i16
            {
                match cbor_pair_is_serialized(x1, x2)
                {
                    option__·CBOR_Pulse_Raw_Type_cbor_serialized···CBOR_Pulse_Raw_Type_cbor_serialized·::Some
                    { v: pair }
                    =>
                      {
                          let res: i16 =
                              cbor_match_compare_serialized_array(
                                  fst__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized(
                                      pair
                                  ),
                                  snd__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized(
                                      pair
                                  )
                              );
                          res
                      },
                    _ =>
                      {
                          let i1: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                              cbor_array_iterator_init(x1);
                          let i2: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                              cbor_array_iterator_init(x2);
                          let pl1: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = i1;
                          let pl2: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = i2;
                          let fin1: bool =
                              match pl1
                              {
                                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice
                                  { _0: c· }
                                  => c·.len() == 0usize,
                                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized
                                  { _0: c· }
                                  => cbor_serialized_array_iterator_is_empty(c·),
                                  _ => panic!("Incomplete pattern matching")
                              };
                          let fin2: bool =
                              match pl2
                              {
                                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice
                                  { _0: c· }
                                  => c·.len() == 0usize,
                                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized
                                  { _0: c· }
                                  => cbor_serialized_array_iterator_is_empty(c·),
                                  _ => panic!("Incomplete pattern matching")
                              };
                          let res: i16 =
                              if fin1
                              { if fin2 { 0i16 } else { -1i16 } }
                              else if fin2
                              { 1i16 }
                              else
                              {
                                  let
                                  mut pi1: [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
                                  =
                                      [pl1; 1usize];
                                  let
                                  mut pi2: [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]
                                  =
                                      [pl2; 1usize];
                                  let mut pres: [i16; 1] = [0i16; 1usize];
                                  let mut pfin1: [bool; 1] = [false; 1usize];
                                  let res: i16 = (&pres)[0];
                                  let fin11: bool = (&pfin1)[0];
                                  let mut cond: bool = res == 0i16 && ! fin11;
                                  while
                                  cond
                                  {
                                      let i0: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                                          (&pi1)[0];
                                      let elt1: cbor_raw =
                                          match i0
                                          {
                                              cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice
                                              { _0: i }
                                              =>
                                                {
                                                    let res0: cbor_raw = i[0usize];
                                                    let _letpattern: (&[cbor_raw], &[cbor_raw]) =
                                                        i.split_at(1usize);
                                                    let s·: &[cbor_raw] =
                                                        {
                                                            let _s1: &[cbor_raw] = _letpattern.0;
                                                            let s2: &[cbor_raw] = _letpattern.1;
                                                            s2
                                                        };
                                                    let i11: &[cbor_raw] = s·;
                                                    let i·: &[cbor_raw] = i11;
                                                    (&mut pi1)[0] =
                                                        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice
                                                        { _0: i· };
                                                    let res1: cbor_raw = res0;
                                                    res1
                                                },
                                              cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized
                                              { _0: i }
                                              =>
                                                {
                                                    let res0: cbor_raw =
                                                        cbor_serialized_array_iterator_next(
                                                            &mut pi1,
                                                            i
                                                        );
                                                    res0
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          };
                                      let i00: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                                          (&pi2)[0];
                                      let elt2: cbor_raw =
                                          match i00
                                          {
                                              cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice
                                              { _0: i }
                                              =>
                                                {
                                                    let res0: cbor_raw = i[0usize];
                                                    let _letpattern: (&[cbor_raw], &[cbor_raw]) =
                                                        i.split_at(1usize);
                                                    let s·: &[cbor_raw] =
                                                        {
                                                            let _s1: &[cbor_raw] = _letpattern.0;
                                                            let s2: &[cbor_raw] = _letpattern.1;
                                                            s2
                                                        };
                                                    let i11: &[cbor_raw] = s·;
                                                    let i·: &[cbor_raw] = i11;
                                                    (&mut pi2)[0] =
                                                        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice
                                                        { _0: i· };
                                                    let res1: cbor_raw = res0;
                                                    res1
                                                },
                                              cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized
                                              { _0: i }
                                              =>
                                                {
                                                    let res0: cbor_raw =
                                                        cbor_serialized_array_iterator_next(
                                                            &mut pi2,
                                                            i
                                                        );
                                                    res0
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          };
                                      let pelt1: cbor_raw = elt1;
                                      let pelt2: cbor_raw = elt2;
                                      let c2: i16 = impl_cbor_compare(pelt1, pelt2);
                                      if c2 == 0i16
                                      {
                                          let i11: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                                              (&pi1)[0];
                                          let fin110: bool =
                                              match i11
                                              {
                                                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice
                                                  { _0: c· }
                                                  => c·.len() == 0usize,
                                                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized
                                                  { _0: c· }
                                                  => cbor_serialized_array_iterator_is_empty(c·),
                                                  _ => panic!("Incomplete pattern matching")
                                              };
                                          let i21: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                                              (&pi2)[0];
                                          let fin21: bool =
                                              match i21
                                              {
                                                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice
                                                  { _0: c· }
                                                  => c·.len() == 0usize,
                                                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized
                                                  { _0: c· }
                                                  => cbor_serialized_array_iterator_is_empty(c·),
                                                  _ => panic!("Incomplete pattern matching")
                                              };
                                          if fin110 == fin21
                                          { (&mut pfin1)[0] = fin110 }
                                          else if fin110
                                          { (&mut pres)[0] = -1i16 }
                                          else
                                          { (&mut pres)[0] = 1i16 }
                                      }
                                      else
                                      { (&mut pres)[0] = c2 };
                                      let res0: i16 = (&pres)[0];
                                      let fin110: bool = (&pfin1)[0];
                                      cond = res0 == 0i16 && ! fin110
                                  };
                                  (&pres)[0]
                              };
                          let res0: i16 = res;
                          res0
                      }
                }
            }
            else
            { c1 }
        }
        else if ty1 == cbor_major_type_map
        {
            let len1: raw_uint64 =
                match x1
                {
                    cbor_raw::CBOR_Case_Map { v: c· } =>
                      raw_uint64
                      { size: c·.cbor_map_length_size, value: (c·.cbor_map_ptr).len() as u64 },
                    cbor_raw::CBOR_Case_Serialized_Map { v: c· } => c·.cbor_serialized_header,
                    _ => panic!("Incomplete pattern matching")
                };
            let len2: raw_uint64 =
                match x2
                {
                    cbor_raw::CBOR_Case_Map { v: c· } =>
                      raw_uint64
                      { size: c·.cbor_map_length_size, value: (c·.cbor_map_ptr).len() as u64 },
                    cbor_raw::CBOR_Case_Serialized_Map { v: c· } => c·.cbor_serialized_header,
                    _ => panic!("Incomplete pattern matching")
                };
            let c1: i16 = impl_raw_uint64_compare(len1, len2);
            if c1 == 0i16
            {
                match cbor_pair_is_serialized(x1, x2)
                {
                    option__·CBOR_Pulse_Raw_Type_cbor_serialized···CBOR_Pulse_Raw_Type_cbor_serialized·::Some
                    { v: pair }
                    =>
                      {
                          let res: i16 =
                              cbor_match_compare_serialized_map(
                                  fst__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized(
                                      pair
                                  ),
                                  snd__CBOR_Pulse_Raw_Type_cbor_serialized_CBOR_Pulse_Raw_Type_cbor_serialized(
                                      pair
                                  )
                              );
                          res
                      },
                    _ =>
                      {
                          let i1: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
                              cbor_map_iterator_init(x1);
                          let i2: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
                              cbor_map_iterator_init(x2);
                          let pl1: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry = i1;
                          let pl2: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry = i2;
                          let fin1: bool =
                              match pl1
                              {
                                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
                                  { _0: c· }
                                  => c·.len() == 0usize,
                                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
                                  { _0: c· }
                                  => cbor_serialized_map_iterator_is_empty(c·),
                                  _ => panic!("Incomplete pattern matching")
                              };
                          let fin2: bool =
                              match pl2
                              {
                                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
                                  { _0: c· }
                                  => c·.len() == 0usize,
                                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
                                  { _0: c· }
                                  => cbor_serialized_map_iterator_is_empty(c·),
                                  _ => panic!("Incomplete pattern matching")
                              };
                          let res: i16 =
                              if fin1
                              { if fin2 { 0i16 } else { -1i16 } }
                              else if fin2
                              { 1i16 }
                              else
                              {
                                  let
                                  mut
                                  pi1:
                                  [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry; 1]
                                  =
                                      [pl1; 1usize];
                                  let
                                  mut
                                  pi2:
                                  [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry; 1]
                                  =
                                      [pl2; 1usize];
                                  let mut pres: [i16; 1] = [0i16; 1usize];
                                  let mut pfin1: [bool; 1] = [false; 1usize];
                                  let res: i16 = (&pres)[0];
                                  let fin11: bool = (&pfin1)[0];
                                  let mut cond: bool = res == 0i16 && ! fin11;
                                  while
                                  cond
                                  {
                                      let
                                      i0: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                      =
                                          (&pi1)[0];
                                      let elt1: cbor_map_entry =
                                          match i0
                                          {
                                              cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
                                              { _0: i }
                                              =>
                                                {
                                                    let res0: cbor_map_entry = i[0usize];
                                                    let
                                                    _letpattern:
                                                    (&[cbor_map_entry], &[cbor_map_entry])
                                                    =
                                                        i.split_at(1usize);
                                                    let s·: &[cbor_map_entry] =
                                                        {
                                                            let _s1: &[cbor_map_entry] =
                                                                _letpattern.0;
                                                            let s2: &[cbor_map_entry] =
                                                                _letpattern.1;
                                                            s2
                                                        };
                                                    let i11: &[cbor_map_entry] = s·;
                                                    let i·: &[cbor_map_entry] = i11;
                                                    (&mut pi1)[0] =
                                                        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
                                                        { _0: i· };
                                                    let res1: cbor_map_entry = res0;
                                                    res1
                                                },
                                              cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
                                              { _0: i }
                                              =>
                                                {
                                                    let res0: cbor_map_entry =
                                                        cbor_serialized_map_iterator_next(
                                                            &mut pi1,
                                                            i
                                                        );
                                                    res0
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          };
                                      let
                                      i00: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                      =
                                          (&pi2)[0];
                                      let elt2: cbor_map_entry =
                                          match i00
                                          {
                                              cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
                                              { _0: i }
                                              =>
                                                {
                                                    let res0: cbor_map_entry = i[0usize];
                                                    let
                                                    _letpattern:
                                                    (&[cbor_map_entry], &[cbor_map_entry])
                                                    =
                                                        i.split_at(1usize);
                                                    let s·: &[cbor_map_entry] =
                                                        {
                                                            let _s1: &[cbor_map_entry] =
                                                                _letpattern.0;
                                                            let s2: &[cbor_map_entry] =
                                                                _letpattern.1;
                                                            s2
                                                        };
                                                    let i11: &[cbor_map_entry] = s·;
                                                    let i·: &[cbor_map_entry] = i11;
                                                    (&mut pi2)[0] =
                                                        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
                                                        { _0: i· };
                                                    let res1: cbor_map_entry = res0;
                                                    res1
                                                },
                                              cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
                                              { _0: i }
                                              =>
                                                {
                                                    let res0: cbor_map_entry =
                                                        cbor_serialized_map_iterator_next(
                                                            &mut pi2,
                                                            i
                                                        );
                                                    res0
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          };
                                      let pelt1: cbor_map_entry = elt1;
                                      let pelt2: cbor_map_entry = elt2;
                                      let c2: i16 =
                                          impl_cbor_compare(
                                              pelt1.cbor_map_entry_key,
                                              pelt2.cbor_map_entry_key
                                          );
                                      let c20: i16 =
                                          if c2 == 0i16
                                          {
                                              impl_cbor_compare(
                                                  pelt1.cbor_map_entry_value,
                                                  pelt2.cbor_map_entry_value
                                              )
                                          }
                                          else
                                          { c2 };
                                      if c20 == 0i16
                                      {
                                          let
                                          i11: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                          =
                                              (&pi1)[0];
                                          let fin110: bool =
                                              match i11
                                              {
                                                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
                                                  { _0: c· }
                                                  => c·.len() == 0usize,
                                                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
                                                  { _0: c· }
                                                  => cbor_serialized_map_iterator_is_empty(c·),
                                                  _ => panic!("Incomplete pattern matching")
                                              };
                                          let
                                          i21: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
                                          =
                                              (&pi2)[0];
                                          let fin21: bool =
                                              match i21
                                              {
                                                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
                                                  { _0: c· }
                                                  => c·.len() == 0usize,
                                                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
                                                  { _0: c· }
                                                  => cbor_serialized_map_iterator_is_empty(c·),
                                                  _ => panic!("Incomplete pattern matching")
                                              };
                                          if fin110 == fin21
                                          { (&mut pfin1)[0] = fin110 }
                                          else if fin110
                                          { (&mut pres)[0] = -1i16 }
                                          else
                                          { (&mut pres)[0] = 1i16 }
                                      }
                                      else
                                      { (&mut pres)[0] = c20 };
                                      let res0: i16 = (&pres)[0];
                                      let fin110: bool = (&pfin1)[0];
                                      cond = res0 == 0i16 && ! fin110
                                  };
                                  (&pres)[0]
                              };
                          let res0: i16 = res;
                          res0
                      }
                }
            }
            else
            { c1 }
        }
        else
        {
            let _letpattern: cbor_raw = x1;
            let val1: u8 =
                match _letpattern
                {
                    cbor_raw::CBOR_Case_Simple { v: res } => res,
                    _ => panic!("Incomplete pattern matching")
                };
            let _letpattern0: cbor_raw = x2;
            let val2: u8 =
                match _letpattern0
                {
                    cbor_raw::CBOR_Case_Simple { v: res } => res,
                    _ => panic!("Incomplete pattern matching")
                };
            impl_uint8_compare(val1, val2)
        }
    }
    else
    { c }
}

fn cbor_raw_compare(x1: cbor_raw, x2: cbor_raw) -> i16 { impl_cbor_compare(x1, x2) }

fn cbor_map_entry_raw_compare(x1: cbor_map_entry, x2: cbor_map_entry) -> i16
{ cbor_raw_compare(x1.cbor_map_entry_key, x2.cbor_map_entry_key) }

pub(crate) fn cbor_raw_sort_aux(a: &mut [cbor_map_entry]) -> bool
{
    let len: usize = a.len();
    if len < 2usize
    { true }
    else
    {
        let len_half: usize = len.wrapping_div(2usize);
        let mi: usize = len_half;
        let _letpattern: (&mut [cbor_map_entry], &mut [cbor_map_entry]) = a.split_at_mut(mi);
        let a1: &mut [cbor_map_entry] = _letpattern.0;
        let a2: &mut [cbor_map_entry] = _letpattern.1;
        let res: bool = cbor_raw_sort_aux(a1);
        if ! res
        { false }
        else
        {
            let res1: bool = cbor_raw_sort_aux(a2);
            if ! res1
            { false }
            else
            {
                let mut pi1: [usize; 1] = [0usize; 1usize];
                let mut pi2: [usize; 1] = [mi; 1usize];
                let mut pres: [bool; 1] = [true; 1usize];
                let i1: usize = (&pi1)[0];
                let i2: usize = (&pi2)[0];
                let res2: bool = (&pres)[0];
                let mut cond: bool = res2 && ! (i1 == i2 || i2 == a.len());
                while
                cond
                {
                    let i10: usize = (&pi1)[0];
                    let x1: cbor_map_entry = a[i10];
                    let i20: usize = (&pi2)[0];
                    let x2: cbor_map_entry = a[i20];
                    let comp: i16 = cbor_map_entry_raw_compare(x1, x2);
                    if comp == 0i16
                    { (&mut pres)[0] = false }
                    else if comp < 0i16
                    {
                        let i1·: usize = i10.wrapping_add(1usize);
                        (&mut pi1)[0] = i1·
                    }
                    else
                    {
                        let i2·: usize = i20.wrapping_add(1usize);
                        let _letpattern1: (&mut [cbor_map_entry], &mut [cbor_map_entry]) =
                            a.split_at_mut(i2·);
                        let ac01: &mut [cbor_map_entry] = _letpattern1.0;
                        let _ac2: &[cbor_map_entry] = _letpattern1.1;
                        let _letpattern2: (&mut [cbor_map_entry], &mut [cbor_map_entry]) =
                            ac01.split_at_mut(i10);
                        let _ac: &[cbor_map_entry] = _letpattern2.0;
                        let ac1: &mut [cbor_map_entry] = _letpattern2.1;
                        if ! (i20.wrapping_sub(i10) == 0usize || i20.wrapping_sub(i10) == ac1.len())
                        {
                            let mut pn: [usize; 1] = [ac1.len(); 1usize];
                            let mut pl: [usize; 1] = [i20.wrapping_sub(i10); 1usize];
                            let __anf0: usize = (&pl)[0];
                            let mut cond0: bool = __anf0 > 0usize;
                            while
                            cond0
                            {
                                let n: usize = (&pn)[0];
                                let l3: usize = (&pl)[0];
                                let l·: usize = n.wrapping_rem(l3);
                                (&mut pn)[0] = l3;
                                (&mut pl)[0] = l·;
                                let __anf00: usize = (&pl)[0];
                                cond0 = __anf00 > 0usize
                            };
                            let d: usize = (&pn)[0];
                            let q: usize = ac1.len().wrapping_div(d);
                            let mut pi: [usize; 1] = [0usize; 1usize];
                            let __anf00: usize = (&pi)[0];
                            let mut cond1: bool = __anf00 < d;
                            while
                            cond1
                            {
                                let i: usize = (&pi)[0];
                                let save: cbor_map_entry = ac1[i];
                                let mut pj: [usize; 1] = [0usize; 1usize];
                                let mut pidx: [usize; 1] = [i; 1usize];
                                let __anf01: usize = (&pj)[0];
                                let mut cond2: bool = __anf01 < q.wrapping_sub(1usize);
                                while
                                cond2
                                {
                                    let j: usize = (&pj)[0];
                                    let idx: usize = (&pidx)[0];
                                    let idx·: usize =
                                        if
                                        idx.wrapping_sub(0usize)
                                        >=
                                        ac1.len().wrapping_sub(i20.wrapping_sub(i10))
                                        {
                                            idx.wrapping_sub(
                                                ac1.len().wrapping_sub(i20.wrapping_sub(i10))
                                            )
                                        }
                                        else
                                        {
                                            idx.wrapping_add(
                                                i20.wrapping_sub(i10).wrapping_sub(0usize)
                                            )
                                        };
                                    let x: cbor_map_entry = ac1[idx·];
                                    let j·: usize = j.wrapping_add(1usize);
                                    ac1[idx] = x;
                                    (&mut pj)[0] = j·;
                                    (&mut pidx)[0] = idx·;
                                    let __anf02: usize = (&pj)[0];
                                    cond2 = __anf02 < q.wrapping_sub(1usize)
                                };
                                let idx: usize = (&pidx)[0];
                                ac1[idx] = save;
                                let i·: usize = i.wrapping_add(1usize);
                                (&mut pi)[0] = i·;
                                let __anf02: usize = (&pi)[0];
                                cond1 = __anf02 < d
                            }
                        };
                        let i1·: usize = i10.wrapping_add(1usize);
                        (&mut pi1)[0] = i1·;
                        (&mut pi2)[0] = i2·
                    };
                    let i11: usize = (&pi1)[0];
                    let i21: usize = (&pi2)[0];
                    let res20: bool = (&pres)[0];
                    cond = res20 && ! (i11 == i21 || i21 == a.len())
                };
                let res20: bool = (&pres)[0];
                res20
            }
        }
    }
}

pub(crate) fn cbor_raw_sort(a: &mut [cbor_map_entry]) -> bool { cbor_raw_sort_aux(a) }

pub(crate) fn impl_cbor_det_compare(x1: cbor_raw, x2: cbor_raw) -> i16
{ impl_cbor_compare(x1, x2) }

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

pub type cbor_det_t <'a> = cbor_raw <'a>;

pub type cbor_det_map_entry_t <'a> = cbor_map_entry <'a>;

pub type cbor_det_array_iterator_t <'a> = cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>;

pub type cbor_det_map_iterator_t <'a> =
cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>;

pub fn dummy_cbor_det_t <'a>() -> cbor_raw <'a> { cbor_raw::CBOR_Case_Simple { v: 0u8 } }
