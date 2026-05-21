#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub(crate) const _zero_for_deref: u32 = 0u32;

pub(crate) fn append_n_before_sz(off: usize, n: usize, cb: usize) -> usize
{
    if off >= cb
    { 0usize }
    else
    {
        let diff: usize = cb.wrapping_sub(off);
        if n <= diff { n } else { diff }
    }
}

pub(crate) fn append_n_after_sz(off: usize, n: usize, cb: usize) -> usize
{ n.wrapping_sub(append_n_before_sz(off, n, cb)) }

pub(crate) fn append_off_before_sz(off: usize, ob: usize, cb: usize) -> usize
{
    let ite: usize = if off >= cb { cb } else { off };
    ob.wrapping_add(ite)
}

pub(crate) fn append_off_after_sz(off: usize, oa: usize, ca: usize, cb: usize) -> usize
{
    crate::lowstar::ignore::ignore::<usize>(ca);
    let ite: usize = if off >= cb { off.wrapping_sub(cb) } else { 0usize };
    oa.wrapping_add(ite)
}

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
    (&pres)[0]
}

pub(crate) fn impl_correct(s: &[u8]) -> bool
{
    let mut pres: [bool; 1] = [true; 1usize];
    let mut pi: [usize; 1] = [0usize; 1usize];
    let len: usize = s.len();
    let res: bool = (&pres)[0];
    let i: usize = (&pi)[0];
    let mut cond: bool = res && i < len;
    while
    cond
    {
        let i0: usize = (&pi)[0];
        let byte1: u8 = s[i0];
        let i1: usize = i0.wrapping_add(1usize);
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
        let i2: usize = (&pi)[0];
        cond = res0 && i2 < len
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
    { off1 }
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

pub(crate) fn jump_raw_data_item(input: &[u8], offset: usize) -> usize
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
            { off1 };
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

#[derive(PartialEq, Clone, Copy)]
pub struct cbor_int
{ pub cbor_int_type: u8, pub cbor_int_size: u8, pub cbor_int_value: u64 }

#[derive(PartialEq, Clone, Copy)]
pub struct cbor_string <'a>
{ pub cbor_string_type: u8, pub cbor_string_size: u8, pub cbor_string_ptr: &'a [u8] }

#[derive(PartialEq, Clone, Copy)]
pub struct cbor_tagged__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>
{ pub cbor_tagged_tag: raw_uint64, pub cbor_tagged_ptr: &'a [cbor_raw <'a>] }

#[derive(PartialEq, Clone, Copy)]
pub struct cbor_tagged_serialized <'a>
{ pub cbor_tagged_serialized_tag: raw_uint64, pub cbor_tagged_serialized_ptr: &'a [u8] }

#[derive(PartialEq, Clone, Copy)]
pub struct cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>
{
    pub cbor_array_length_size: u8,
    pub cbor_array_ptr: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>
}

#[derive(PartialEq, Clone, Copy)]
enum cbor_raw_tags
{
    CBOR_Case_Invalid,
    CBOR_Case_Int,
    CBOR_Case_Simple,
    CBOR_Case_String,
    CBOR_Case_Tagged,
    CBOR_Case_Tagged_Serialized,
    CBOR_Case_Array,
    CBOR_Case_Map
}

#[derive(PartialEq, Clone, Copy)]
pub enum cbor_raw <'a>
{
    CBOR_Case_Invalid,
    CBOR_Case_Int { v: cbor_int },
    CBOR_Case_Simple { v: u8 },
    CBOR_Case_String { v: cbor_string <'a> },
    CBOR_Case_Tagged { v: cbor_tagged__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a> },
    CBOR_Case_Tagged_Serialized { v: cbor_tagged_serialized <'a> },
    CBOR_Case_Array { v: cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a> },
    CBOR_Case_Map { v: cbor_map__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a> }
}

#[derive(PartialEq, Clone, Copy)]
pub struct cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>
{ pub cbor_map_entry_key: cbor_raw <'a>, pub cbor_map_entry_value: cbor_raw <'a> }

#[derive(PartialEq, Clone, Copy)]
enum
base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_tags
{
    Empty,
    Singleton,
    Slice,
    Serialized
}

#[derive(PartialEq, Clone, Copy)]
pub enum
base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
<'a>
{
    Empty,
    Singleton { sr: &'a [cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>] },
    Slice { ss: &'a [cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>] },
    Serialized { count: usize, payload: &'a [u8] }
}

#[derive(PartialEq, Clone, Copy)]
enum
mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_tags
{
    Base,
    Append
}

#[derive(PartialEq, Clone, Copy)]
pub enum
mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
<'a>
{
    Base
    {
        _0:
        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        <'a>
    },
    Append
    {
        cb: usize,
        ca: usize,
        ob: usize,
        before:
        &'a [mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        <'a>],
        oa: usize,
        after:
        &'a [mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        <'a>]
    }
}

#[derive(PartialEq, Clone, Copy)]
pub struct cbor_map__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>
{
    pub cbor_map_length_size: u8,
    pub cbor_map_ptr:
    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
}

#[derive(PartialEq, Clone, Copy)]
pub enum cbor_rawÂ· <'a>
{
    CBOR_Case_Invalid,
    CBOR_Case_Int { v: cbor_int },
    CBOR_Case_Simple { v: u8 },
    CBOR_Case_String { v: cbor_string <'a> },
    CBOR_Case_Tagged { v: cbor_tagged__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a> },
    CBOR_Case_Tagged_Serialized { v: cbor_tagged_serialized <'a> },
    CBOR_Case_Array { v: cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a> },
    CBOR_Case_Map { v: cbor_map__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a> }
}

#[derive(PartialEq, Clone, Copy)]
pub enum base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>
{
    Empty,
    Singleton { sr: &'a [cbor_raw <'a>] },
    Slice { ss: &'a [cbor_raw <'a>] },
    Serialized { count: usize, payload: &'a [u8] }
}

#[derive(PartialEq, Clone, Copy)]
pub enum mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>
{
    Base { _0: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a> },
    Append
    {
        cb: usize,
        ca: usize,
        ob: usize,
        before: &'a [mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>],
        oa: usize,
        after: &'a [mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>]
    }
}

#[derive(PartialEq, Clone, Copy)]
pub struct cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_rawÂ· <'a>
{
    pub cbor_array_length_size: u8,
    pub cbor_array_ptr: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>
}

#[derive(PartialEq, Clone, Copy)]
pub enum cbor_rawÂ·Â· <'a>
{
    CBOR_Case_Invalid,
    CBOR_Case_Int { v: cbor_int },
    CBOR_Case_Simple { v: u8 },
    CBOR_Case_String { v: cbor_string <'a> },
    CBOR_Case_Tagged { v: cbor_tagged__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a> },
    CBOR_Case_Tagged_Serialized { v: cbor_tagged_serialized <'a> },
    CBOR_Case_Array { v: cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a> },
    CBOR_Case_Map { v: cbor_map__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a> }
}

fn cbor_raw_read_match_aux <'a>(input: &'a [u8]) -> cbor_raw <'a>
{
    let off1: usize = jump_header(input, 0usize);
    let s·: (&[u8], &[u8]) = input.split_at(off1);
    let _letpattern: (&[u8], &[u8]) =
        {
            let s1: &[u8] = s·.0;
            let s2: &[u8] = s·.1;
            (s1,s2)
        };
    let input1: &[u8] = _letpattern.0;
    let input2: &[u8] = _letpattern.1;
    let v1: header = read_header(input1);
    let b: initial_byte_t =
        dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(v1);
    let la: long_argument =
        dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(v1);
    if b.major_type == cbor_major_type_byte_string || b.major_type == cbor_major_type_text_string
    {
        let n: usize = argument_as_uint64(b, la) as usize;
        let s·0: (&[u8], &[u8]) = input2.split_at(n);
        let input1_input2: (&[u8], &[u8]) =
            {
                let s1: &[u8] = s·0.0;
                let s2: &[u8] = s·0.1;
                (s1,s2)
            };
        let input11: &[u8] = input1_input2.0;
        let _input21: &[u8] = input1_input2.1;
        cbor_raw::CBOR_Case_String
        {
            v:
            cbor_string
            {
                cbor_string_type: b.major_type,
                cbor_string_size:
                match la
                {
                    long_argument::LongArgumentU8 { v: v2 } =>
                      raw_uint64 { size: 1u8, value: v2 as u64 },
                    long_argument::LongArgumentU16 { v: v2 } =>
                      raw_uint64 { size: 2u8, value: v2 as u64 },
                    long_argument::LongArgumentU32 { v: v2 } =>
                      raw_uint64 { size: 3u8, value: v2 as u64 },
                    long_argument::LongArgumentU64 { v: v2 } => raw_uint64 { size: 4u8, value: v2 },
                    long_argument::LongArgumentOther =>
                      raw_uint64 { size: 0u8, value: b.additional_info as u64 },
                    _ => panic!("Incomplete pattern matching")
                }.size,
                cbor_string_ptr: input11
            }
        }
    }
    else if b.major_type == cbor_major_type_array
    {
        let n: usize = argument_as_uint64(b, la) as usize;
        cbor_raw::CBOR_Case_Array
        {
            v:
            cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            {
                cbor_array_length_size:
                match la
                {
                    long_argument::LongArgumentU8 { v: v2 } =>
                      raw_uint64 { size: 1u8, value: v2 as u64 },
                    long_argument::LongArgumentU16 { v: v2 } =>
                      raw_uint64 { size: 2u8, value: v2 as u64 },
                    long_argument::LongArgumentU32 { v: v2 } =>
                      raw_uint64 { size: 3u8, value: v2 as u64 },
                    long_argument::LongArgumentU64 { v: v2 } => raw_uint64 { size: 4u8, value: v2 },
                    long_argument::LongArgumentOther =>
                      raw_uint64 { size: 0u8, value: b.additional_info as u64 },
                    _ => panic!("Incomplete pattern matching")
                }.size,
                cbor_array_ptr:
                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                {
                    _0:
                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                    { count: n, payload: input2 }
                }
            }
        }
    }
    else if b.major_type == cbor_major_type_map
    {
        let n: usize = argument_as_uint64(b, la) as usize;
        cbor_raw::CBOR_Case_Map
        {
            v:
            cbor_map__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
            {
                cbor_map_length_size:
                match la
                {
                    long_argument::LongArgumentU8 { v: v2 } =>
                      raw_uint64 { size: 1u8, value: v2 as u64 },
                    long_argument::LongArgumentU16 { v: v2 } =>
                      raw_uint64 { size: 2u8, value: v2 as u64 },
                    long_argument::LongArgumentU32 { v: v2 } =>
                      raw_uint64 { size: 3u8, value: v2 as u64 },
                    long_argument::LongArgumentU64 { v: v2 } => raw_uint64 { size: 4u8, value: v2 },
                    long_argument::LongArgumentOther =>
                      raw_uint64 { size: 0u8, value: b.additional_info as u64 },
                    _ => panic!("Incomplete pattern matching")
                }.size,
                cbor_map_ptr:
                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                {
                    _0:
                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                    { count: n, payload: input2 }
                }
            }
        }
    }
    else if b.major_type == cbor_major_type_tagged
    {
        cbor_raw::CBOR_Case_Tagged_Serialized
        {
            v:
            cbor_tagged_serialized
            {
                cbor_tagged_serialized_tag:
                match la
                {
                    long_argument::LongArgumentU8 { v: v2 } =>
                      raw_uint64 { size: 1u8, value: v2 as u64 },
                    long_argument::LongArgumentU16 { v: v2 } =>
                      raw_uint64 { size: 2u8, value: v2 as u64 },
                    long_argument::LongArgumentU32 { v: v2 } =>
                      raw_uint64 { size: 3u8, value: v2 as u64 },
                    long_argument::LongArgumentU64 { v: v2 } => raw_uint64 { size: 4u8, value: v2 },
                    long_argument::LongArgumentOther =>
                      raw_uint64 { size: 0u8, value: b.additional_info as u64 },
                    _ => panic!("Incomplete pattern matching")
                },
                cbor_tagged_serialized_ptr: input2
            }
        }
    }
    else if b.major_type == cbor_major_type_simple_value
    {
        cbor_raw::CBOR_Case_Simple
        {
            v:
            match la
            {
                long_argument::LongArgumentOther => b.additional_info,
                long_argument::LongArgumentSimpleValue { v: v2 } => v2,
                _ => panic!("Incomplete pattern matching")
            }
        }
    }
    else
    {
        cbor_raw::CBOR_Case_Int
        {
            v:
            cbor_int
            {
                cbor_int_type: b.major_type,
                cbor_int_size:
                match la
                {
                    long_argument::LongArgumentU8 { v: v2 } =>
                      raw_uint64 { size: 1u8, value: v2 as u64 },
                    long_argument::LongArgumentU16 { v: v2 } =>
                      raw_uint64 { size: 2u8, value: v2 as u64 },
                    long_argument::LongArgumentU32 { v: v2 } =>
                      raw_uint64 { size: 3u8, value: v2 as u64 },
                    long_argument::LongArgumentU64 { v: v2 } => raw_uint64 { size: 4u8, value: v2 },
                    long_argument::LongArgumentOther =>
                      raw_uint64 { size: 0u8, value: b.additional_info as u64 },
                    _ => panic!("Incomplete pattern matching")
                }.size,
                cbor_int_value:
                match la
                {
                    long_argument::LongArgumentU8 { v: v2 } =>
                      raw_uint64 { size: 1u8, value: v2 as u64 },
                    long_argument::LongArgumentU16 { v: v2 } =>
                      raw_uint64 { size: 2u8, value: v2 as u64 },
                    long_argument::LongArgumentU32 { v: v2 } =>
                      raw_uint64 { size: 3u8, value: v2 as u64 },
                    long_argument::LongArgumentU64 { v: v2 } => raw_uint64 { size: 4u8, value: v2 },
                    long_argument::LongArgumentOther =>
                      raw_uint64 { size: 0u8, value: b.additional_info as u64 },
                    _ => panic!("Incomplete pattern matching")
                }.value
            }
        }
    }
}

pub(crate) fn cbor_raw_read <'a>(input: &'a [u8]) -> cbor_raw <'a>
{
    let res: cbor_raw = cbor_raw_read_match_aux(input);
    res
}

fn cbor_raw_read_fuel <'a>(input: &'a [u8]) -> cbor_raw <'a>
{
    let res: cbor_raw = cbor_raw_read_match_aux(input);
    res
}

#[derive(PartialEq, Clone, Copy)]
enum option__uint8_t_tags
{
    None,
    Some
}

#[derive(PartialEq, Clone, Copy)]
enum option__uint8_t
{
    None,
    Some { v: u8 }
}

fn cbor_raw_get_major_type_aux(x: cbor_raw) -> u8
{
    match
    match x
    {
        cbor_raw::CBOR_Case_Int { v } => option__uint8_t::Some { v: v.cbor_int_type },
        cbor_raw::CBOR_Case_Simple { .. } =>
          option__uint8_t::Some { v: cbor_major_type_simple_value },
        cbor_raw::CBOR_Case_String { v } => option__uint8_t::Some { v: v.cbor_string_type },
        cbor_raw::CBOR_Case_Array { .. } => option__uint8_t::Some { v: cbor_major_type_array },
        cbor_raw::CBOR_Case_Map { .. } => option__uint8_t::Some { v: cbor_major_type_map },
        cbor_raw::CBOR_Case_Tagged { .. } => option__uint8_t::Some { v: cbor_major_type_tagged },
        cbor_raw::CBOR_Case_Tagged_Serialized { .. } =>
          option__uint8_t::Some { v: cbor_major_type_tagged },
        cbor_raw::CBOR_Case_Invalid => option__uint8_t::None,
        _ => panic!("Incomplete pattern matching")
    }
    { option__uint8_t::Some { v } => v, _ => panic!("Incomplete pattern matching") }
}

pub(crate) fn cbor_raw_get_major_type(x: cbor_raw) -> u8 { cbor_raw_get_major_type_aux(x) }

fn cbor_raw_get_string_aux <'a>(x: cbor_raw <'a>) -> &'a [u8]
{
    match x
    {
        cbor_raw::CBOR_Case_String { v } => v.cbor_string_ptr,
        cbor_raw::CBOR_Case_Invalid => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Int { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Simple { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Array { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Map { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Tagged { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Tagged_Serialized { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        _ => panic!("Incomplete pattern matching")
    }
}

pub(crate) fn cbor_raw_get_string <'a>(x: cbor_raw <'a>) -> &'a [u8]
{
    let s: &[u8] = cbor_raw_get_string_aux(x);
    s
}

pub(crate) fn cbor_raw_get_tagged_payload <'a>(x: cbor_raw <'a>) -> cbor_raw <'a>
{
    match x
    {
        cbor_raw::CBOR_Case_Tagged { v } => v.cbor_tagged_ptr[0],
        cbor_raw::CBOR_Case_Tagged_Serialized { v: ts } =>
          {
              let res: cbor_raw = cbor_raw_read(ts.cbor_tagged_serialized_ptr);
              res
          },
        cbor_raw::CBOR_Case_Invalid => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Int { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Simple { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_String { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Array { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Map { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
enum elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_tags
{
    EElement,
    ESerialized
}

#[derive(PartialEq, Clone, Copy)]
pub(crate) enum elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>
{
    EElement { _0: cbor_raw <'a> },
    ESerialized { _0: &'a [u8] }
}

fn cbor_raw_get_tagged_payload_aux_eos <'a>(x: cbor_raw <'a>) ->
    elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    match x
    {
        cbor_raw::CBOR_Case_Tagged { v } =>
          {
              let res: cbor_raw = v.cbor_tagged_ptr[0];
              elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::EElement { _0: res }
          },
        cbor_raw::CBOR_Case_Tagged_Serialized { v: ts } =>
          elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::ESerialized
          { _0: ts.cbor_tagged_serialized_ptr },
        cbor_raw::CBOR_Case_Invalid => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Int { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Simple { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_String { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Array { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Map { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        _ => panic!("Incomplete pattern matching")
    }
}

fn cbor_raw_get_array_aux <'a>(x: cbor_raw <'a>) ->
    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    match x
    {
        cbor_raw::CBOR_Case_Array { v } => v.cbor_array_ptr,
        cbor_raw::CBOR_Case_Invalid => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Int { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Simple { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_String { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Map { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Tagged { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Tagged_Serialized { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        _ => panic!("Incomplete pattern matching")
    }
}

pub(crate) fn cbor_raw_get_array <'a>(x: cbor_raw <'a>) ->
    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    let res: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw = cbor_raw_get_array_aux(x);
    res
}

fn cbor_raw_get_map_aux <'a>(x: cbor_raw <'a>) ->
    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    match x
    {
        cbor_raw::CBOR_Case_Map { v } => v.cbor_map_ptr,
        cbor_raw::CBOR_Case_Invalid => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Int { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Simple { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_String { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Array { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Tagged { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        cbor_raw::CBOR_Case_Tagged_Serialized { .. } => panic!("Pulse.Lib.Dv.unreachable"),
        _ => panic!("Incomplete pattern matching")
    }
}

pub(crate) fn cbor_raw_get_map <'a>(x: cbor_raw <'a>) ->
    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    let
    res:
    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    =
        cbor_raw_get_map_aux(x);
    res
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
                    argument_as_uint64(b0, l) as usize
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
                let x: header = read_header(input·);
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
                    { off1 };
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
                let n·: usize = n0.wrapping_sub(1usize).wrapping_add(count);
                (&mut pn)[0] = n·;
                (&mut ppi)[0] = pc
            };
            let res1: bool = (&pres)[0];
            let n1: usize = (&pn)[0];
            cond = res1 && n1 > 0usize
        };
        let check1: bool = (&pres)[0];
        if ! check1
        { 0usize }
        else
        {
            let mut pn0: [usize; 1] = [1usize; 1usize];
            let mut pres0: [bool; 1] = [true; 1usize];
            let mut ppi0: [&[u8]; 1] = [input1; 1usize];
            let res0: bool = (&pres0)[0];
            let n0: usize = (&pn0)[0];
            let mut cond0: bool = res0 && n0 > 0usize;
            while
            cond0
            {
                let n1: usize = (&pn0)[0];
                let pi: &[u8] = (&ppi0)[0];
                let res1: bool = cbor_raw_sorted(pi);
                if ! res1
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
                    let x: header = read_header(input·);
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
                        { off1 };
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
                    let n·: usize = n1.wrapping_sub(1usize).wrapping_add(count);
                    (&mut pn0)[0] = n·;
                    (&mut ppi0)[0] = pc
                };
                let res2: bool = (&pres0)[0];
                let n2: usize = (&pn0)[0];
                cond0 = res2 && n2 > 0usize
            };
            let check2: bool = (&pres0)[0];
            if ! check2 { 0usize } else { len }
        }
    }
}

pub(crate) fn cbor_validate_det(input: &[u8]) -> usize { cbor_validate_det·(input) }

pub(crate) fn cbor_parse_valid <'a>(input: &'a [u8]) -> cbor_raw <'a>
{
    let len: usize = input.len();
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
    cbor_raw_read(input1)
}

fn cbor_raw_reset_perm_tot <'a>(c: cbor_raw <'a>) -> cbor_raw <'a>
{
    match c
    {
        cbor_raw::CBOR_Case_String { v } =>
          cbor_raw::CBOR_Case_String
          {
              v:
              cbor_string
              {
                  cbor_string_type: v.cbor_string_type,
                  cbor_string_size: v.cbor_string_size,
                  cbor_string_ptr: v.cbor_string_ptr
              }
          },
        cbor_raw::CBOR_Case_Tagged { v } =>
          cbor_raw::CBOR_Case_Tagged
          {
              v:
              cbor_tagged__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              { cbor_tagged_tag: v.cbor_tagged_tag, cbor_tagged_ptr: v.cbor_tagged_ptr }
          },
        cbor_raw::CBOR_Case_Tagged_Serialized { v } =>
          cbor_raw::CBOR_Case_Tagged_Serialized
          {
              v:
              cbor_tagged_serialized
              {
                  cbor_tagged_serialized_tag: v.cbor_tagged_serialized_tag,
                  cbor_tagged_serialized_ptr: v.cbor_tagged_serialized_ptr
              }
          },
        cbor_raw::CBOR_Case_Array { v } =>
          cbor_raw::CBOR_Case_Array
          {
              v:
              cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              { cbor_array_length_size: v.cbor_array_length_size, cbor_array_ptr: v.cbor_array_ptr }
          },
        cbor_raw::CBOR_Case_Map { v } =>
          cbor_raw::CBOR_Case_Map
          {
              v:
              cbor_map__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
              { cbor_map_length_size: v.cbor_map_length_size, cbor_map_ptr: v.cbor_map_ptr }
          },
        _ => c
    }
}

pub(crate) fn cbor_raw_reset_perm <'a>(c: cbor_raw <'a>) -> cbor_raw <'a>
{ cbor_raw_reset_perm_tot(c) }

pub(crate) fn cbor_mk_simple_value <'a>(v: u8) -> cbor_raw <'a>
{ cbor_raw::CBOR_Case_Simple { v } }

pub(crate) fn cbor_mk_int64 <'a>(ty: u8, v: u64) -> cbor_raw <'a>
{
    let i: cbor_int =
        cbor_int { cbor_int_type: ty, cbor_int_size: (mk_raw_uint64(v)).size, cbor_int_value: v };
    cbor_raw::CBOR_Case_Int { v: i }
}

pub(crate) fn cbor_mk_string <'a>(ty: u8, s: &'a [u8]) -> cbor_raw <'a>
{
    let len64: u64 = s.len() as u64;
    let ru: raw_uint64 = mk_raw_uint64(len64);
    let str: cbor_string =
        cbor_string { cbor_string_type: ty, cbor_string_size: ru.size, cbor_string_ptr: s };
    cbor_raw::CBOR_Case_String { v: str }
}

pub(crate) fn cbor_mk_tagged <'a>(tag: u64, r: &'a [cbor_raw <'a>]) -> cbor_raw <'a>
{
    let ru: raw_uint64 = mk_raw_uint64(tag);
    let tv: cbor_tagged__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
        cbor_tagged__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        { cbor_tagged_tag: ru, cbor_tagged_ptr: r };
    cbor_raw::CBOR_Case_Tagged { v: tv }
}

pub(crate) fn cbor_mk_map_entry <'a>(xk: cbor_raw <'a>, xv: cbor_raw <'a>) ->
    cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    { cbor_map_entry_key: xk, cbor_map_entry_value: xv }
}

pub(crate) fn base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
    i: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
) ->
    usize
{
    match i
    {
        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty => 0usize,
        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton { .. } => 1usize,
        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice { ss: sl } => sl.len(),
        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized { count, .. } => count,
        _ => panic!("Incomplete pattern matching")
    }
}

pub(crate) fn mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
    i: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
) ->
    usize
{
    match i
    {
        mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base { _0: bi } =>
          base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(bi),
        mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append { cb, ca, .. } =>
          cb.wrapping_add(ca),
        _ => panic!("Incomplete pattern matching")
    }
}

pub(crate) fn cbor_mk_array <'a>(
    len_size: u8,
    ml: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>
) ->
    cbor_raw
    <'a>
{
    let len_sz: usize = mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ml);
    crate::lowstar::ignore::ignore::<usize>(len_sz);
    let v: cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
        cbor_array__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        { cbor_array_length_size: len_size, cbor_array_ptr: ml };
    cbor_raw::CBOR_Case_Array { v }
}

pub(crate) fn
base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
    i:
    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
) ->
    usize
{
    match i
    {
        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
        => 0usize,
        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
        { .. }
        => 1usize,
        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
        { ss: sl }
        => sl.len(),
        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
        { count, .. }
        => count,
        _ => panic!("Incomplete pattern matching")
    }
}

pub(crate) fn
mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
    i:
    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
) ->
    usize
{
    match i
    {
        mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
        { _0: bi }
        =>
          base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
              bi
          ),
        mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
        { cb, ca, .. }
        => cb.wrapping_add(ca),
        _ => panic!("Incomplete pattern matching")
    }
}

pub(crate) fn cbor_mk_map <'a>(
    len_size: u8,
    ml:
    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
) ->
    cbor_raw
    <'a>
{
    let len_sz: usize =
        mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
            ml
        );
    crate::lowstar::ignore::ignore::<usize>(len_sz);
    let v: cbor_map__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
        cbor_map__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
        { cbor_map_length_size: len_size, cbor_map_ptr: ml };
    cbor_raw::CBOR_Case_Map { v }
}

pub(crate) fn cbor_raw_read_map_entry <'a>(input: &'a [u8]) ->
    cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    let off1: usize = jump_raw_data_item(input, 0usize);
    let s·: (&[u8], &[u8]) = input.split_at(off1);
    let _letpattern: (&[u8], &[u8]) =
        {
            let s1: &[u8] = s·.0;
            let s2: &[u8] = s·.1;
            (s1,s2)
        };
    let split_input: (&[u8], &[u8]) =
        {
            let input1: &[u8] = _letpattern.0;
            let input2: &[u8] = _letpattern.1;
            (input1,input2)
        };
    let input1: &[u8] = split_input.0;
    let input2: &[u8] = split_input.1;
    let xk: cbor_raw = cbor_raw_read(input1);
    let xv: cbor_raw = cbor_raw_read(input2);
    cbor_mk_map_entry(xk, xv)
}

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
    let off: usize = (&poff)[0];
    let mut cond: bool = uu___is_CInProgress(res) && off < off2;
    while
    cond
    {
        let off0: usize = (&poff)[0];
        let sp_top: (&mut [u8], &mut [u8]) = out.split_at_mut(off0);
        {
            let _out1: &[u8] = sp_top.0;
            let out2kv: &mut [u8] = sp_top.1;
            let sp_kv: (&[u8], &[u8]) = out2kv.split_at(off2.wrapping_sub(off0));
            let out2: &[u8] = sp_kv.0;
            let outkv: &[u8] = sp_kv.1;
            let sp_v: (&[u8], &[u8]) = outkv.split_at(off3.wrapping_sub(off2));
            let outk: &[u8] = sp_v.0;
            let _outv: &[u8] = sp_v.1;
            let offk: usize = jump_raw_data_item(out2, 0usize);
            let sp_k: (&[u8], &[u8]) = out2.split_at(offk);
            let outk·: &[u8] = sp_k.0;
            let outvq: &[u8] = sp_k.1;
            let c: i16 = lex_compare_bytes(outk·, outk);
            if c < 0i16
            {
                let offq: usize = jump_raw_data_item(outvq, 0usize);
                let off·: usize = off0.wrapping_add(offk.wrapping_add(offq));
                (&mut poff)[0] = off·
            }
            else if c > 0i16
            {
                if ! (off2.wrapping_sub(off0) == 0usize || off2.wrapping_sub(off0) == out2kv.len())
                {
                    let mut pn: [usize; 1] = [out2kv.len(); 1usize];
                    let mut pl: [usize; 1] = [off2.wrapping_sub(off0); 1usize];
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
                                out2kv.len().wrapping_sub(off2.wrapping_sub(off0))
                                {
                                    idx.wrapping_sub(
                                        out2kv.len().wrapping_sub(off2.wrapping_sub(off0))
                                    )
                                }
                                else
                                { idx.wrapping_add(off2.wrapping_sub(off0).wrapping_sub(0usize)) };
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
        let off1: usize = (&poff)[0];
        cond = uu___is_CInProgress(res0) && off1 < off2
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

#[derive(PartialEq, Clone, Copy)]
enum option__CBOR_Spec_Raw_EverParse_header
{
    None,
    Some { v: header }
}

fn cbor_raw_get_header_impl(xl: cbor_raw) -> header
{
    let _letpattern: option__CBOR_Spec_Raw_EverParse_header =
        match xl
        {
            cbor_raw::CBOR_Case_Int { v } =>
              option__CBOR_Spec_Raw_EverParse_header::Some
              {
                  v:
                  raw_uint64_as_argument(
                      v.cbor_int_type,
                      raw_uint64 { size: v.cbor_int_size, value: v.cbor_int_value }
                  )
              },
            cbor_raw::CBOR_Case_Simple { v } =>
              option__CBOR_Spec_Raw_EverParse_header::Some { v: simple_value_as_argument(v) },
            cbor_raw::CBOR_Case_String { v } =>
              option__CBOR_Spec_Raw_EverParse_header::Some
              {
                  v:
                  raw_uint64_as_argument(
                      v.cbor_string_type,
                      raw_uint64
                      { size: v.cbor_string_size, value: (v.cbor_string_ptr).len() as u64 }
                  )
              },
            cbor_raw::CBOR_Case_Array { v } =>
              option__CBOR_Spec_Raw_EverParse_header::Some
              {
                  v:
                  raw_uint64_as_argument(
                      cbor_major_type_array,
                      raw_uint64
                      {
                          size: v.cbor_array_length_size,
                          value:
                          mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                              v.cbor_array_ptr
                          )
                          as
                          u64
                      }
                  )
              },
            cbor_raw::CBOR_Case_Map { v } =>
              option__CBOR_Spec_Raw_EverParse_header::Some
              {
                  v:
                  raw_uint64_as_argument(
                      cbor_major_type_map,
                      raw_uint64
                      {
                          size: v.cbor_map_length_size,
                          value:
                          mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                              v.cbor_map_ptr
                          )
                          as
                          u64
                      }
                  )
              },
            cbor_raw::CBOR_Case_Tagged { v } =>
              option__CBOR_Spec_Raw_EverParse_header::Some
              { v: raw_uint64_as_argument(cbor_major_type_tagged, v.cbor_tagged_tag) },
            cbor_raw::CBOR_Case_Tagged_Serialized { v } =>
              option__CBOR_Spec_Raw_EverParse_header::Some
              { v: raw_uint64_as_argument(cbor_major_type_tagged, v.cbor_tagged_serialized_tag) },
            cbor_raw::CBOR_Case_Invalid => option__CBOR_Spec_Raw_EverParse_header::None,
            _ => panic!("Incomplete pattern matching")
        };
    match _letpattern
    {
        option__CBOR_Spec_Raw_EverParse_header::Some { v: res } => res,
        _ => panic!("Incomplete pattern matching")
    }
}

fn cbor_raw_with_perm_get_header(xl: cbor_raw) -> header { cbor_raw_get_header_impl(xl) }

pub(crate) fn uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
    projectee: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
) ->
    bool
{
    match projectee
    { mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base { .. } => true, _ => false }
}

pub(crate) fn
fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
<'a>(x: (base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>, usize)) ->
    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    let _1: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw = x.0;
    let __2: usize = x.1;
    _1
}

pub(crate) fn
snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
    x: (base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw, usize)
) ->
    usize
{
    let __1: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw = x.0;
    let _2: usize = x.1;
    _2
}

pub(crate) fn
uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
    projectee:
    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
) ->
    bool
{
    match projectee
    {
        mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
        { .. }
        => true,
        _ => false
    }
}

pub(crate) fn
fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t
<'a>(
    x:
    (base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>,
    usize)
) ->
    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
{
    let
    _1:
    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    =
        x.0;
    let __2: usize = x.1;
    _1
}

pub(crate) fn
snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
    x:
    (base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
    usize)
) ->
    usize
{
    let
    __1:
    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    =
        x.0;
    let _2: usize = x.1;
    _2
}

pub(crate) fn ser·(x·: cbor_raw, out: &mut [u8], offset: usize) -> usize
{
    let xh1: header = cbor_raw_with_perm_get_header(x·);
    let res1: usize = write_header(xh1, out, offset);
    let b: initial_byte_t = xh1.fst;
    if b.major_type == cbor_major_type_byte_string || b.major_type == cbor_major_type_text_string
    {
        let s: &[u8] = cbor_raw_get_string(x·);
        let x2·: &[u8] = s;
        let length: usize = x2·.len();
        let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(res1);
        let _sp11: &[u8] = _letpattern.0;
        let sp12: &mut [u8] = _letpattern.1;
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
            let arr: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw = cbor_raw_get_array(x·);
            let n: usize = argument_as_uint64(xh1.fst, xh1.snd) as usize;
            if n == 0usize
            { res1 }
            else
            {
                let mut p_node: [mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw; 1] =
                    [arr; 1usize];
                let mut p_offset: [usize; 1] = [res1; 1usize];
                let mut p_remaining: [usize; 1] = [n; 1usize];
                let rem: usize = (&p_remaining)[0];
                let mut cond: bool = rem > 0usize;
                while
                cond
                {
                    let cur: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw = (&p_node)[0];
                    let cur_off: usize = (&p_offset)[0];
                    let cur_rem: usize = (&p_remaining)[0];
                    let mut r_node: [mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw; 1] =
                        [cur; 1usize];
                    let mut r_off: [usize; 1] = [0usize; 1usize];
                    let mut r_n: [usize; 1] = [cur_rem; 1usize];
                    let mut pcontinue: [bool; 1] =
                        [! uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(cur); 1usize];
                    while
                    (&pcontinue)[0]
                    {
                        let node: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw = (&r_node)[0];
                        let cur_off_v: usize = (&r_off)[0];
                        let cur_n_v: usize = (&r_n)[0];
                        match node
                        {
                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                            { cb, ca, ob, before, oa, after }
                            =>
                              {
                                  let child_n_before: usize =
                                      append_n_before_sz(cur_off_v, cur_n_v, cb);
                                  if child_n_before > 0usize
                                  {
                                      let child_off_sz: usize =
                                          append_off_before_sz(cur_off_v, ob, cb);
                                      let ib: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                                          before[0];
                                      (&mut r_node)[0] = ib;
                                      (&mut r_off)[0] = child_off_sz;
                                      (&mut r_n)[0] = child_n_before;
                                      (&mut pcontinue)[0] =
                                          ! uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ib)
                                  }
                                  else
                                  {
                                      let child_off_sz: usize =
                                          append_off_after_sz(cur_off_v, oa, ca, cb);
                                      let child_n_sz: usize =
                                          append_n_after_sz(cur_off_v, cur_n_v, cb);
                                      let ia: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                                          after[0];
                                      (&mut r_node)[0] = ia;
                                      (&mut r_off)[0] = child_off_sz;
                                      (&mut r_n)[0] = child_n_sz;
                                      (&mut pcontinue)[0] =
                                          ! uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ia)
                                  }
                              },
                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base { .. } => (),
                            _ => panic!("Incomplete pattern matching")
                        }
                    };
                    let node: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw = (&r_node)[0];
                    let cur_off_v: usize = (&r_off)[0];
                    let cur_n_v: usize = (&r_n)[0];
                    let res: (base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw, usize) =
                        match node
                        {
                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base { _0: bi } =>
                              {
                                  let
                                  bi·: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                  =
                                      match bi
                                      {
                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                          =>
                                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                          { sr: s }
                                          =>
                                            if cur_n_v == 0usize
                                            {
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                            }
                                            else
                                            {
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                { sr: s }
                                            },
                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                          { ss: s }
                                          =>
                                            {
                                                let s_pr: (&[cbor_raw], &[cbor_raw]) =
                                                    s.split_at(cur_off_v);
                                                let _s_prefix: &[cbor_raw] = s_pr.0;
                                                let s_rest: &[cbor_raw] = s_pr.1;
                                                let s_ms: (&[cbor_raw], &[cbor_raw]) =
                                                    s_rest.split_at(cur_n_v);
                                                let s_middle: &[cbor_raw] = s_ms.0;
                                                let _s_suffix: &[cbor_raw] = s_ms.1;
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                { ss: s_middle }
                                            },
                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                          { payload: pl, .. }
                                          =>
                                            {
                                                let mut pn: [usize; 1] = [cur_off_v; 1usize];
                                                let mut poffset: [usize; 1] = [0usize; 1usize];
                                                let n1: usize = (&pn)[0];
                                                let mut cond0: bool = n1 > 0usize;
                                                while
                                                cond0
                                                {
                                                    let n10: usize = (&pn)[0];
                                                    let offset2: usize = (&poffset)[0];
                                                    let offset·: usize =
                                                        jump_raw_data_item(pl, offset2);
                                                    (&mut pn)[0] = n10.wrapping_sub(1usize);
                                                    (&mut poffset)[0] = offset·;
                                                    let n11: usize = (&pn)[0];
                                                    cond0 = n11 > 0usize
                                                };
                                                let pos: usize = (&poffset)[0];
                                                let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                                let _pl_prefix: &[u8] = pl_p.0;
                                                let pl_suffix: &[u8] = pl_p.1;
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                { count: cur_n_v, payload: pl_suffix }
                                            },
                                          _ => panic!("Incomplete pattern matching")
                                      };
                                  let len: usize =
                                      base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                          bi·
                                      );
                                  (bi·,len)
                              },
                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append { .. } =>
                              panic!("Pulse.Lib.Dv.unreachable"),
                            _ => panic!("Incomplete pattern matching")
                        };
                    let bi: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                        fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                            res
                        );
                    let chunk_len: usize =
                        snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                            res
                        );
                    match bi
                    {
                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                        { payload: pl_bi, .. }
                        =>
                          {
                              let mut pn: [usize; 1] = [chunk_len; 1usize];
                              let mut poffset: [usize; 1] = [0usize; 1usize];
                              let n1: usize = (&pn)[0];
                              let mut cond0: bool = n1 > 0usize;
                              while
                              cond0
                              {
                                  let n10: usize = (&pn)[0];
                                  let offset2: usize = (&poffset)[0];
                                  let offset·: usize = jump_raw_data_item(pl_bi, offset2);
                                  (&mut pn)[0] = n10.wrapping_sub(1usize);
                                  (&mut poffset)[0] = offset·;
                                  let n11: usize = (&pn)[0];
                                  cond0 = n11 > 0usize
                              };
                              let byte_len: usize = (&poffset)[0];
                              let _letpattern: (&mut [u8], &mut [u8]) = out.split_at_mut(cur_off);
                              let off·: usize =
                                  {
                                      let _out11: &[u8] = _letpattern.0;
                                      let out2: &mut [u8] = _letpattern.1;
                                      let _letpattern1: (&mut [u8], &mut [u8]) =
                                          out2.split_at_mut(byte_len);
                                      let out21: &mut [u8] = _letpattern1.0;
                                      let _out22: &[u8] = _letpattern1.1;
                                      let _letpattern2: (&[u8], &[u8]) = pl_bi.split_at(byte_len);
                                      let pl1: &[u8] = _letpattern2.0;
                                      let _pl2: &[u8] = _letpattern2.1;
                                      out21.copy_from_slice(pl1);
                                      cur_off.wrapping_add(byte_len)
                                  };
                              let new_rem: usize = cur_rem.wrapping_sub(chunk_len);
                              let new_node: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                                  match cur
                                  {
                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                      { _0: bi1 }
                                      =>
                                        {
                                            let
                                            bi·:
                                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                            =
                                                match bi1
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                    =>
                                                      base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                    { sr: s }
                                                    =>
                                                      if new_rem == 0usize
                                                      {
                                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                      }
                                                      else
                                                      {
                                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                          { sr: s }
                                                      },
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                    { ss: s }
                                                    =>
                                                      {
                                                          let s_pr: (&[cbor_raw], &[cbor_raw]) =
                                                              s.split_at(chunk_len);
                                                          let _s_prefix: &[cbor_raw] = s_pr.0;
                                                          let s_rest: &[cbor_raw] = s_pr.1;
                                                          let s_ms: (&[cbor_raw], &[cbor_raw]) =
                                                              s_rest.split_at(new_rem);
                                                          let s_middle: &[cbor_raw] = s_ms.0;
                                                          let _s_suffix: &[cbor_raw] = s_ms.1;
                                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                          { ss: s_middle }
                                                      },
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                    { payload: pl, .. }
                                                    =>
                                                      {
                                                          let mut pn0: [usize; 1] =
                                                              [chunk_len; 1usize];
                                                          let mut poffset0: [usize; 1] =
                                                              [0usize; 1usize];
                                                          let n10: usize = (&pn0)[0];
                                                          let mut cond1: bool = n10 > 0usize;
                                                          while
                                                          cond1
                                                          {
                                                              let n11: usize = (&pn0)[0];
                                                              let offset2: usize = (&poffset0)[0];
                                                              let offset·: usize =
                                                                  jump_raw_data_item(pl, offset2);
                                                              (&mut pn0)[0] =
                                                                  n11.wrapping_sub(1usize);
                                                              (&mut poffset0)[0] = offset·;
                                                              let n12: usize = (&pn0)[0];
                                                              cond1 = n12 > 0usize
                                                          };
                                                          let pos: usize = (&poffset0)[0];
                                                          let pl_p: (&[u8], &[u8]) =
                                                              pl.split_at(pos);
                                                          let _pl_prefix: &[u8] = pl_p.0;
                                                          let pl_suffix: &[u8] = pl_p.1;
                                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                          { count: new_rem, payload: pl_suffix }
                                                      },
                                                    _ => panic!("Incomplete pattern matching")
                                                };
                                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                            { _0: bi· }
                                        },
                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                      { cb, ca, ob, before, oa, after }
                                      =>
                                        {
                                            let cb·_sz: usize =
                                                append_n_before_sz(chunk_len, new_rem, cb);
                                            let ca·_sz: usize =
                                                append_n_after_sz(chunk_len, new_rem, cb);
                                            let ob·_sz: usize =
                                                append_off_before_sz(chunk_len, ob, cb);
                                            let oa·_sz: usize =
                                                append_off_after_sz(chunk_len, oa, ca, cb);
                                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                            {
                                                cb: cb·_sz,
                                                ca: ca·_sz,
                                                ob: ob·_sz,
                                                before,
                                                oa: oa·_sz,
                                                after
                                            }
                                        },
                                      _ => panic!("Incomplete pattern matching")
                                  };
                              (&mut p_node)[0] = new_node;
                              (&mut p_offset)[0] = off·;
                              (&mut p_remaining)[0] = new_rem
                          },
                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                        { ss: ss_bi }
                        =>
                          {
                              let mut pres: [usize; 1] = [cur_off; 1usize];
                              let mut pi: [usize; 1] = [0usize; 1usize];
                              let i1: usize = (&pi)[0];
                              let mut cond0: bool = i1 < chunk_len;
                              while
                              cond0
                              {
                                  let i10: usize = (&pi)[0];
                                  let off: usize = (&pres)[0];
                                  let e: cbor_raw = ss_bi[i10];
                                  let i·: usize = i10.wrapping_add(1usize);
                                  let x2·: cbor_raw = e;
                                  let off·: usize = ser·(x2·, out, off);
                                  (&mut pi)[0] = i·;
                                  (&mut pres)[0] = off·;
                                  let i11: usize = (&pi)[0];
                                  cond0 = i11 < chunk_len
                              };
                              let off·: usize = (&pres)[0];
                              let new_rem: usize = cur_rem.wrapping_sub(chunk_len);
                              let new_node: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                                  match cur
                                  {
                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                      { _0: bi1 }
                                      =>
                                        {
                                            let
                                            bi·:
                                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                            =
                                                match bi1
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                    =>
                                                      base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                    { sr: s }
                                                    =>
                                                      if new_rem == 0usize
                                                      {
                                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                      }
                                                      else
                                                      {
                                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                          { sr: s }
                                                      },
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                    { ss: s }
                                                    =>
                                                      {
                                                          let s_pr: (&[cbor_raw], &[cbor_raw]) =
                                                              s.split_at(chunk_len);
                                                          let _s_prefix: &[cbor_raw] = s_pr.0;
                                                          let s_rest: &[cbor_raw] = s_pr.1;
                                                          let s_ms: (&[cbor_raw], &[cbor_raw]) =
                                                              s_rest.split_at(new_rem);
                                                          let s_middle: &[cbor_raw] = s_ms.0;
                                                          let _s_suffix: &[cbor_raw] = s_ms.1;
                                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                          { ss: s_middle }
                                                      },
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                    { payload: pl, .. }
                                                    =>
                                                      {
                                                          let mut pn: [usize; 1] =
                                                              [chunk_len; 1usize];
                                                          let mut poffset: [usize; 1] =
                                                              [0usize; 1usize];
                                                          let n1: usize = (&pn)[0];
                                                          let mut cond1: bool = n1 > 0usize;
                                                          while
                                                          cond1
                                                          {
                                                              let n10: usize = (&pn)[0];
                                                              let offset2: usize = (&poffset)[0];
                                                              let offset·: usize =
                                                                  jump_raw_data_item(pl, offset2);
                                                              (&mut pn)[0] =
                                                                  n10.wrapping_sub(1usize);
                                                              (&mut poffset)[0] = offset·;
                                                              let n11: usize = (&pn)[0];
                                                              cond1 = n11 > 0usize
                                                          };
                                                          let pos: usize = (&poffset)[0];
                                                          let pl_p: (&[u8], &[u8]) =
                                                              pl.split_at(pos);
                                                          let _pl_prefix: &[u8] = pl_p.0;
                                                          let pl_suffix: &[u8] = pl_p.1;
                                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                          { count: new_rem, payload: pl_suffix }
                                                      },
                                                    _ => panic!("Incomplete pattern matching")
                                                };
                                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                            { _0: bi· }
                                        },
                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                      { cb, ca, ob, before, oa, after }
                                      =>
                                        {
                                            let cb·_sz: usize =
                                                append_n_before_sz(chunk_len, new_rem, cb);
                                            let ca·_sz: usize =
                                                append_n_after_sz(chunk_len, new_rem, cb);
                                            let ob·_sz: usize =
                                                append_off_before_sz(chunk_len, ob, cb);
                                            let oa·_sz: usize =
                                                append_off_after_sz(chunk_len, oa, ca, cb);
                                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                            {
                                                cb: cb·_sz,
                                                ca: ca·_sz,
                                                ob: ob·_sz,
                                                before,
                                                oa: oa·_sz,
                                                after
                                            }
                                        },
                                      _ => panic!("Incomplete pattern matching")
                                  };
                              (&mut p_node)[0] = new_node;
                              (&mut p_offset)[0] = off·;
                              (&mut p_remaining)[0] = new_rem
                          },
                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                        { sr: sr_bi }
                        =>
                          {
                              let xv: cbor_raw = sr_bi[0];
                              let x2·: cbor_raw = xv;
                              let off·: usize = ser·(x2·, out, cur_off);
                              let new_rem: usize = cur_rem.wrapping_sub(chunk_len);
                              let new_node: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                                  match cur
                                  {
                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                      { _0: bi1 }
                                      =>
                                        {
                                            let
                                            bi·:
                                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                            =
                                                match bi1
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                    =>
                                                      base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                    { sr: s }
                                                    =>
                                                      if new_rem == 0usize
                                                      {
                                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                      }
                                                      else
                                                      {
                                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                          { sr: s }
                                                      },
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                    { ss: s }
                                                    =>
                                                      {
                                                          let s_pr: (&[cbor_raw], &[cbor_raw]) =
                                                              s.split_at(chunk_len);
                                                          let _s_prefix: &[cbor_raw] = s_pr.0;
                                                          let s_rest: &[cbor_raw] = s_pr.1;
                                                          let s_ms: (&[cbor_raw], &[cbor_raw]) =
                                                              s_rest.split_at(new_rem);
                                                          let s_middle: &[cbor_raw] = s_ms.0;
                                                          let _s_suffix: &[cbor_raw] = s_ms.1;
                                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                          { ss: s_middle }
                                                      },
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                    { payload: pl, .. }
                                                    =>
                                                      {
                                                          let mut pn: [usize; 1] =
                                                              [chunk_len; 1usize];
                                                          let mut poffset: [usize; 1] =
                                                              [0usize; 1usize];
                                                          let n1: usize = (&pn)[0];
                                                          let mut cond0: bool = n1 > 0usize;
                                                          while
                                                          cond0
                                                          {
                                                              let n10: usize = (&pn)[0];
                                                              let offset2: usize = (&poffset)[0];
                                                              let offset·: usize =
                                                                  jump_raw_data_item(pl, offset2);
                                                              (&mut pn)[0] =
                                                                  n10.wrapping_sub(1usize);
                                                              (&mut poffset)[0] = offset·;
                                                              let n11: usize = (&pn)[0];
                                                              cond0 = n11 > 0usize
                                                          };
                                                          let pos: usize = (&poffset)[0];
                                                          let pl_p: (&[u8], &[u8]) =
                                                              pl.split_at(pos);
                                                          let _pl_prefix: &[u8] = pl_p.0;
                                                          let pl_suffix: &[u8] = pl_p.1;
                                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                          { count: new_rem, payload: pl_suffix }
                                                      },
                                                    _ => panic!("Incomplete pattern matching")
                                                };
                                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                            { _0: bi· }
                                        },
                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                      { cb, ca, ob, before, oa, after }
                                      =>
                                        {
                                            let cb·_sz: usize =
                                                append_n_before_sz(chunk_len, new_rem, cb);
                                            let ca·_sz: usize =
                                                append_n_after_sz(chunk_len, new_rem, cb);
                                            let ob·_sz: usize =
                                                append_off_before_sz(chunk_len, ob, cb);
                                            let oa·_sz: usize =
                                                append_off_after_sz(chunk_len, oa, ca, cb);
                                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                            {
                                                cb: cb·_sz,
                                                ca: ca·_sz,
                                                ob: ob·_sz,
                                                before,
                                                oa: oa·_sz,
                                                after
                                            }
                                        },
                                      _ => panic!("Incomplete pattern matching")
                                  };
                              (&mut p_node)[0] = new_node;
                              (&mut p_offset)[0] = off·;
                              (&mut p_remaining)[0] = new_rem
                          },
                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty => (),
                        _ => panic!("Incomplete pattern matching")
                    };
                    let rem0: usize = (&p_remaining)[0];
                    cond = rem0 > 0usize
                };
                (&p_offset)[0]
            }
        }
        else
        {
            let b1: initial_byte_t = xh1.fst;
            if b1.major_type == cbor_major_type_map
            {
                let
                arr:
                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                =
                    cbor_raw_get_map(x·);
                let n: usize = argument_as_uint64(xh1.fst, xh1.snd) as usize;
                if n == 0usize
                { res1 }
                else
                {
                    let
                    mut
                    p_node:
                    [mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;
                    1]
                    =
                        [arr; 1usize];
                    let mut p_offset: [usize; 1] = [res1; 1usize];
                    let mut p_remaining: [usize; 1] = [n; 1usize];
                    let rem: usize = (&p_remaining)[0];
                    let mut cond: bool = rem > 0usize;
                    while
                    cond
                    {
                        let
                        cur:
                        mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                        =
                            (&p_node)[0];
                        let cur_off: usize = (&p_offset)[0];
                        let cur_rem: usize = (&p_remaining)[0];
                        let
                        mut
                        r_node:
                        [mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;
                        1]
                        =
                            [cur; 1usize];
                        let mut r_off: [usize; 1] = [0usize; 1usize];
                        let mut r_n: [usize; 1] = [cur_rem; 1usize];
                        let mut pcontinue: [bool; 1] =
                            [!
                                uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                    cur
                                );
                                1usize];
                        while
                        (&pcontinue)[0]
                        {
                            let
                            node:
                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                            =
                                (&r_node)[0];
                            let cur_off_v: usize = (&r_off)[0];
                            let cur_n_v: usize = (&r_n)[0];
                            match node
                            {
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                { cb, ca, ob, before, oa, after }
                                =>
                                  {
                                      let child_n_before: usize =
                                          append_n_before_sz(cur_off_v, cur_n_v, cb);
                                      if child_n_before > 0usize
                                      {
                                          let child_off_sz: usize =
                                              append_off_before_sz(cur_off_v, ob, cb);
                                          let
                                          ib:
                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                          =
                                              before[0];
                                          (&mut r_node)[0] = ib;
                                          (&mut r_off)[0] = child_off_sz;
                                          (&mut r_n)[0] = child_n_before;
                                          (&mut pcontinue)[0] =
                                              !
                                              uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                  ib
                                              )
                                      }
                                      else
                                      {
                                          let child_off_sz: usize =
                                              append_off_after_sz(cur_off_v, oa, ca, cb);
                                          let child_n_sz: usize =
                                              append_n_after_sz(cur_off_v, cur_n_v, cb);
                                          let
                                          ia:
                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                          =
                                              after[0];
                                          (&mut r_node)[0] = ia;
                                          (&mut r_off)[0] = child_off_sz;
                                          (&mut r_n)[0] = child_n_sz;
                                          (&mut pcontinue)[0] =
                                              !
                                              uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                  ia
                                              )
                                      }
                                  },
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                { .. }
                                => (),
                                _ => panic!("Incomplete pattern matching")
                            }
                        };
                        let
                        node:
                        mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                        =
                            (&r_node)[0];
                        let cur_off_v: usize = (&r_off)[0];
                        let cur_n_v: usize = (&r_n)[0];
                        let
                        res:
                        (base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                        usize)
                        =
                            match node
                            {
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                { _0: bi }
                                =>
                                  {
                                      let
                                      bi·:
                                      base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                      =
                                          match bi
                                          {
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                              =>
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                              { sr: s }
                                              =>
                                                if cur_n_v == 0usize
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                }
                                                else
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                    { sr: s }
                                                },
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                              { ss: s }
                                              =>
                                                {
                                                    let
                                                    s_pr:
                                                    (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                    =
                                                        s.split_at(cur_off_v);
                                                    let
                                                    _s_prefix:
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                    =
                                                        s_pr.0;
                                                    let
                                                    s_rest:
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                    =
                                                        s_pr.1;
                                                    let
                                                    s_ms:
                                                    (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                    =
                                                        s_rest.split_at(cur_n_v);
                                                    let
                                                    s_middle:
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                    =
                                                        s_ms.0;
                                                    let
                                                    _s_suffix:
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                    =
                                                        s_ms.1;
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                    { ss: s_middle }
                                                },
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                              { payload: pl, .. }
                                              =>
                                                {
                                                    let mut pn: [usize; 1] = [cur_off_v; 1usize];
                                                    let mut poffset: [usize; 1] = [0usize; 1usize];
                                                    let n1: usize = (&pn)[0];
                                                    let mut cond0: bool = n1 > 0usize;
                                                    while
                                                    cond0
                                                    {
                                                        let n10: usize = (&pn)[0];
                                                        let offset2: usize = (&poffset)[0];
                                                        let off1: usize =
                                                            jump_raw_data_item(pl, offset2);
                                                        let offset·: usize =
                                                            jump_raw_data_item(pl, off1);
                                                        (&mut pn)[0] = n10.wrapping_sub(1usize);
                                                        (&mut poffset)[0] = offset·;
                                                        let n11: usize = (&pn)[0];
                                                        cond0 = n11 > 0usize
                                                    };
                                                    let pos: usize = (&poffset)[0];
                                                    let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                                    let _pl_prefix: &[u8] = pl_p.0;
                                                    let pl_suffix: &[u8] = pl_p.1;
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                    { count: cur_n_v, payload: pl_suffix }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          };
                                      let len: usize =
                                          base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                              bi·
                                          );
                                      (bi·,len)
                                  },
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                { .. }
                                => panic!("Pulse.Lib.Dv.unreachable"),
                                _ => panic!("Incomplete pattern matching")
                            };
                        let
                        bi:
                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                        =
                            fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                res
                            );
                        let chunk_len: usize =
                            snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                res
                            );
                        match bi
                        {
                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                            { payload: pl_bi, .. }
                            =>
                              {
                                  let mut pn: [usize; 1] = [chunk_len; 1usize];
                                  let mut poffset: [usize; 1] = [0usize; 1usize];
                                  let n1: usize = (&pn)[0];
                                  let mut cond0: bool = n1 > 0usize;
                                  while
                                  cond0
                                  {
                                      let n10: usize = (&pn)[0];
                                      let offset2: usize = (&poffset)[0];
                                      let off1: usize = jump_raw_data_item(pl_bi, offset2);
                                      let offset·: usize = jump_raw_data_item(pl_bi, off1);
                                      (&mut pn)[0] = n10.wrapping_sub(1usize);
                                      (&mut poffset)[0] = offset·;
                                      let n11: usize = (&pn)[0];
                                      cond0 = n11 > 0usize
                                  };
                                  let byte_len: usize = (&poffset)[0];
                                  let _letpattern: (&mut [u8], &mut [u8]) =
                                      out.split_at_mut(cur_off);
                                  let off·: usize =
                                      {
                                          let _out11: &[u8] = _letpattern.0;
                                          let out2: &mut [u8] = _letpattern.1;
                                          let _letpattern1: (&mut [u8], &mut [u8]) =
                                              out2.split_at_mut(byte_len);
                                          let out21: &mut [u8] = _letpattern1.0;
                                          let _out22: &[u8] = _letpattern1.1;
                                          let _letpattern2: (&[u8], &[u8]) =
                                              pl_bi.split_at(byte_len);
                                          let pl1: &[u8] = _letpattern2.0;
                                          let _pl2: &[u8] = _letpattern2.1;
                                          out21.copy_from_slice(pl1);
                                          cur_off.wrapping_add(byte_len)
                                      };
                                  let new_rem: usize = cur_rem.wrapping_sub(chunk_len);
                                  let
                                  new_node:
                                  mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                  =
                                      match cur
                                      {
                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                          { _0: bi1 }
                                          =>
                                            {
                                                let
                                                bi·:
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                =
                                                    match bi1
                                                    {
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                        =>
                                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                        { sr: s }
                                                        =>
                                                          if new_rem == 0usize
                                                          {
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                          }
                                                          else
                                                          {
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                              { sr: s }
                                                          },
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                        { ss: s }
                                                        =>
                                                          {
                                                              let
                                                              s_pr:
                                                              (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                              =
                                                                  s.split_at(chunk_len);
                                                              let
                                                              _s_prefix:
                                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                              =
                                                                  s_pr.0;
                                                              let
                                                              s_rest:
                                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                              =
                                                                  s_pr.1;
                                                              let
                                                              s_ms:
                                                              (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                              =
                                                                  s_rest.split_at(new_rem);
                                                              let
                                                              s_middle:
                                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                              =
                                                                  s_ms.0;
                                                              let
                                                              _s_suffix:
                                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                              =
                                                                  s_ms.1;
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                              { ss: s_middle }
                                                          },
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                        { payload: pl, .. }
                                                        =>
                                                          {
                                                              let mut pn0: [usize; 1] =
                                                                  [chunk_len; 1usize];
                                                              let mut poffset0: [usize; 1] =
                                                                  [0usize; 1usize];
                                                              let n10: usize = (&pn0)[0];
                                                              let mut cond1: bool = n10 > 0usize;
                                                              while
                                                              cond1
                                                              {
                                                                  let n11: usize = (&pn0)[0];
                                                                  let offset2: usize =
                                                                      (&poffset0)[0];
                                                                  let off1: usize =
                                                                      jump_raw_data_item(
                                                                          pl,
                                                                          offset2
                                                                      );
                                                                  let offset·: usize =
                                                                      jump_raw_data_item(pl, off1);
                                                                  (&mut pn0)[0] =
                                                                      n11.wrapping_sub(1usize);
                                                                  (&mut poffset0)[0] = offset·;
                                                                  let n12: usize = (&pn0)[0];
                                                                  cond1 = n12 > 0usize
                                                              };
                                                              let pos: usize = (&poffset0)[0];
                                                              let pl_p: (&[u8], &[u8]) =
                                                                  pl.split_at(pos);
                                                              let _pl_prefix: &[u8] = pl_p.0;
                                                              let pl_suffix: &[u8] = pl_p.1;
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                              { count: new_rem, payload: pl_suffix }
                                                          },
                                                        _ => panic!("Incomplete pattern matching")
                                                    };
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                { _0: bi· }
                                            },
                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                          { cb, ca, ob, before, oa, after }
                                          =>
                                            {
                                                let cb·_sz: usize =
                                                    append_n_before_sz(chunk_len, new_rem, cb);
                                                let ca·_sz: usize =
                                                    append_n_after_sz(chunk_len, new_rem, cb);
                                                let ob·_sz: usize =
                                                    append_off_before_sz(chunk_len, ob, cb);
                                                let oa·_sz: usize =
                                                    append_off_after_sz(chunk_len, oa, ca, cb);
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                {
                                                    cb: cb·_sz,
                                                    ca: ca·_sz,
                                                    ob: ob·_sz,
                                                    before,
                                                    oa: oa·_sz,
                                                    after
                                                }
                                            },
                                          _ => panic!("Incomplete pattern matching")
                                      };
                                  (&mut p_node)[0] = new_node;
                                  (&mut p_offset)[0] = off·;
                                  (&mut p_remaining)[0] = new_rem
                              },
                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                            { ss: ss_bi }
                            =>
                              {
                                  let mut pres: [usize; 1] = [cur_off; 1usize];
                                  let mut pi: [usize; 1] = [0usize; 1usize];
                                  let i1: usize = (&pi)[0];
                                  let mut cond0: bool = i1 < chunk_len;
                                  while
                                  cond0
                                  {
                                      let i10: usize = (&pi)[0];
                                      let off: usize = (&pres)[0];
                                      let
                                      e: cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                      =
                                          ss_bi[i10];
                                      let i·: usize = i10.wrapping_add(1usize);
                                      let x11: cbor_raw = e.cbor_map_entry_key;
                                      let res11: usize = ser·(x11, out, off);
                                      let x2: cbor_raw = e.cbor_map_entry_value;
                                      let off·: usize = ser·(x2, out, res11);
                                      (&mut pi)[0] = i·;
                                      (&mut pres)[0] = off·;
                                      let i11: usize = (&pi)[0];
                                      cond0 = i11 < chunk_len
                                  };
                                  let off·: usize = (&pres)[0];
                                  let new_rem: usize = cur_rem.wrapping_sub(chunk_len);
                                  let
                                  new_node:
                                  mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                  =
                                      match cur
                                      {
                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                          { _0: bi1 }
                                          =>
                                            {
                                                let
                                                bi·:
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                =
                                                    match bi1
                                                    {
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                        =>
                                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                        { sr: s }
                                                        =>
                                                          if new_rem == 0usize
                                                          {
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                          }
                                                          else
                                                          {
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                              { sr: s }
                                                          },
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                        { ss: s }
                                                        =>
                                                          {
                                                              let
                                                              s_pr:
                                                              (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                              =
                                                                  s.split_at(chunk_len);
                                                              let
                                                              _s_prefix:
                                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                              =
                                                                  s_pr.0;
                                                              let
                                                              s_rest:
                                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                              =
                                                                  s_pr.1;
                                                              let
                                                              s_ms:
                                                              (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                              =
                                                                  s_rest.split_at(new_rem);
                                                              let
                                                              s_middle:
                                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                              =
                                                                  s_ms.0;
                                                              let
                                                              _s_suffix:
                                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                              =
                                                                  s_ms.1;
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                              { ss: s_middle }
                                                          },
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                        { payload: pl, .. }
                                                        =>
                                                          {
                                                              let mut pn: [usize; 1] =
                                                                  [chunk_len; 1usize];
                                                              let mut poffset: [usize; 1] =
                                                                  [0usize; 1usize];
                                                              let n1: usize = (&pn)[0];
                                                              let mut cond1: bool = n1 > 0usize;
                                                              while
                                                              cond1
                                                              {
                                                                  let n10: usize = (&pn)[0];
                                                                  let offset2: usize =
                                                                      (&poffset)[0];
                                                                  let off1: usize =
                                                                      jump_raw_data_item(
                                                                          pl,
                                                                          offset2
                                                                      );
                                                                  let offset·: usize =
                                                                      jump_raw_data_item(pl, off1);
                                                                  (&mut pn)[0] =
                                                                      n10.wrapping_sub(1usize);
                                                                  (&mut poffset)[0] = offset·;
                                                                  let n11: usize = (&pn)[0];
                                                                  cond1 = n11 > 0usize
                                                              };
                                                              let pos: usize = (&poffset)[0];
                                                              let pl_p: (&[u8], &[u8]) =
                                                                  pl.split_at(pos);
                                                              let _pl_prefix: &[u8] = pl_p.0;
                                                              let pl_suffix: &[u8] = pl_p.1;
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                              { count: new_rem, payload: pl_suffix }
                                                          },
                                                        _ => panic!("Incomplete pattern matching")
                                                    };
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                { _0: bi· }
                                            },
                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                          { cb, ca, ob, before, oa, after }
                                          =>
                                            {
                                                let cb·_sz: usize =
                                                    append_n_before_sz(chunk_len, new_rem, cb);
                                                let ca·_sz: usize =
                                                    append_n_after_sz(chunk_len, new_rem, cb);
                                                let ob·_sz: usize =
                                                    append_off_before_sz(chunk_len, ob, cb);
                                                let oa·_sz: usize =
                                                    append_off_after_sz(chunk_len, oa, ca, cb);
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                {
                                                    cb: cb·_sz,
                                                    ca: ca·_sz,
                                                    ob: ob·_sz,
                                                    before,
                                                    oa: oa·_sz,
                                                    after
                                                }
                                            },
                                          _ => panic!("Incomplete pattern matching")
                                      };
                                  (&mut p_node)[0] = new_node;
                                  (&mut p_offset)[0] = off·;
                                  (&mut p_remaining)[0] = new_rem
                              },
                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                            { sr: sr_bi }
                            =>
                              {
                                  let xv: cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                                      sr_bi[0];
                                  let x11: cbor_raw = xv.cbor_map_entry_key;
                                  let res11: usize = ser·(x11, out, cur_off);
                                  let x2: cbor_raw = xv.cbor_map_entry_value;
                                  let off·: usize = ser·(x2, out, res11);
                                  let new_rem: usize = cur_rem.wrapping_sub(chunk_len);
                                  let
                                  new_node:
                                  mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                  =
                                      match cur
                                      {
                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                          { _0: bi1 }
                                          =>
                                            {
                                                let
                                                bi·:
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                =
                                                    match bi1
                                                    {
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                        =>
                                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                        { sr: s }
                                                        =>
                                                          if new_rem == 0usize
                                                          {
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                          }
                                                          else
                                                          {
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                              { sr: s }
                                                          },
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                        { ss: s }
                                                        =>
                                                          {
                                                              let
                                                              s_pr:
                                                              (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                              =
                                                                  s.split_at(chunk_len);
                                                              let
                                                              _s_prefix:
                                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                              =
                                                                  s_pr.0;
                                                              let
                                                              s_rest:
                                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                              =
                                                                  s_pr.1;
                                                              let
                                                              s_ms:
                                                              (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                              =
                                                                  s_rest.split_at(new_rem);
                                                              let
                                                              s_middle:
                                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                              =
                                                                  s_ms.0;
                                                              let
                                                              _s_suffix:
                                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                              =
                                                                  s_ms.1;
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                              { ss: s_middle }
                                                          },
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                        { payload: pl, .. }
                                                        =>
                                                          {
                                                              let mut pn: [usize; 1] =
                                                                  [chunk_len; 1usize];
                                                              let mut poffset: [usize; 1] =
                                                                  [0usize; 1usize];
                                                              let n1: usize = (&pn)[0];
                                                              let mut cond0: bool = n1 > 0usize;
                                                              while
                                                              cond0
                                                              {
                                                                  let n10: usize = (&pn)[0];
                                                                  let offset2: usize =
                                                                      (&poffset)[0];
                                                                  let off1: usize =
                                                                      jump_raw_data_item(
                                                                          pl,
                                                                          offset2
                                                                      );
                                                                  let offset·: usize =
                                                                      jump_raw_data_item(pl, off1);
                                                                  (&mut pn)[0] =
                                                                      n10.wrapping_sub(1usize);
                                                                  (&mut poffset)[0] = offset·;
                                                                  let n11: usize = (&pn)[0];
                                                                  cond0 = n11 > 0usize
                                                              };
                                                              let pos: usize = (&poffset)[0];
                                                              let pl_p: (&[u8], &[u8]) =
                                                                  pl.split_at(pos);
                                                              let _pl_prefix: &[u8] = pl_p.0;
                                                              let pl_suffix: &[u8] = pl_p.1;
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                              { count: new_rem, payload: pl_suffix }
                                                          },
                                                        _ => panic!("Incomplete pattern matching")
                                                    };
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                { _0: bi· }
                                            },
                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                          { cb, ca, ob, before, oa, after }
                                          =>
                                            {
                                                let cb·_sz: usize =
                                                    append_n_before_sz(chunk_len, new_rem, cb);
                                                let ca·_sz: usize =
                                                    append_n_after_sz(chunk_len, new_rem, cb);
                                                let ob·_sz: usize =
                                                    append_off_before_sz(chunk_len, ob, cb);
                                                let oa·_sz: usize =
                                                    append_off_after_sz(chunk_len, oa, ca, cb);
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                {
                                                    cb: cb·_sz,
                                                    ca: ca·_sz,
                                                    ob: ob·_sz,
                                                    before,
                                                    oa: oa·_sz,
                                                    after
                                                }
                                            },
                                          _ => panic!("Incomplete pattern matching")
                                      };
                                  (&mut p_node)[0] = new_node;
                                  (&mut p_offset)[0] = off·;
                                  (&mut p_remaining)[0] = new_rem
                              },
                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                            => (),
                            _ => panic!("Incomplete pattern matching")
                        };
                        let rem0: usize = (&p_remaining)[0];
                        cond = rem0 > 0usize
                    };
                    (&p_offset)[0]
                }
            }
            else
            {
                let b2: initial_byte_t = xh1.fst;
                if b2.major_type == cbor_major_type_tagged
                {
                    let payload: cbor_raw = cbor_raw_get_tagged_payload(x·);
                    let x2·: cbor_raw = payload;
                    ser·(x2·, out, res1)
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
            let s: &[u8] = cbor_raw_get_string(x·);
            let x2·: &[u8] = s;
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
                let arr: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                    cbor_raw_get_array(x·);
                let n: usize = argument_as_uint64(xh1.fst, xh1.snd) as usize;
                if n == 0usize
                { true }
                else
                {
                    let mut p_node: [mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw; 1] =
                        [arr; 1usize];
                    let mut p_remaining: [usize; 1] = [n; 1usize];
                    let mut p_result: [bool; 1] = [true; 1usize];
                    let res: bool = (&p_result)[0];
                    let rem: usize = (&p_remaining)[0];
                    let mut cond: bool = res && rem > 0usize;
                    while
                    cond
                    {
                        let cur: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw = (&p_node)[0];
                        let cur_rem: usize = (&p_remaining)[0];
                        let mut r_node: [mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw; 1] =
                            [cur; 1usize];
                        let mut r_off: [usize; 1] = [0usize; 1usize];
                        let mut r_n: [usize; 1] = [cur_rem; 1usize];
                        let mut pcontinue: [bool; 1] =
                            [! uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(cur); 1usize];
                        while
                        (&pcontinue)[0]
                        {
                            let node: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                                (&r_node)[0];
                            let cur_off_v: usize = (&r_off)[0];
                            let cur_n_v: usize = (&r_n)[0];
                            match node
                            {
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                { cb, ca, ob, before, oa, after }
                                =>
                                  {
                                      let child_n_before: usize =
                                          append_n_before_sz(cur_off_v, cur_n_v, cb);
                                      if child_n_before > 0usize
                                      {
                                          let child_off_sz: usize =
                                              append_off_before_sz(cur_off_v, ob, cb);
                                          let
                                          ib: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                          =
                                              before[0];
                                          (&mut r_node)[0] = ib;
                                          (&mut r_off)[0] = child_off_sz;
                                          (&mut r_n)[0] = child_n_before;
                                          (&mut pcontinue)[0] =
                                              !
                                              uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                  ib
                                              )
                                      }
                                      else
                                      {
                                          let child_off_sz: usize =
                                              append_off_after_sz(cur_off_v, oa, ca, cb);
                                          let child_n_sz: usize =
                                              append_n_after_sz(cur_off_v, cur_n_v, cb);
                                          let
                                          ia: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                          =
                                              after[0];
                                          (&mut r_node)[0] = ia;
                                          (&mut r_off)[0] = child_off_sz;
                                          (&mut r_n)[0] = child_n_sz;
                                          (&mut pcontinue)[0] =
                                              !
                                              uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                  ia
                                              )
                                      }
                                  },
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base { .. } =>
                                  (),
                                _ => panic!("Incomplete pattern matching")
                            }
                        };
                        let node: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw = (&r_node)[0];
                        let cur_off_v: usize = (&r_off)[0];
                        let cur_n_v: usize = (&r_n)[0];
                        let res0: (base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw, usize) =
                            match node
                            {
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                { _0: bi }
                                =>
                                  {
                                      let
                                      bi·: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                      =
                                          match bi
                                          {
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                              =>
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                              { sr: s }
                                              =>
                                                if cur_n_v == 0usize
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                }
                                                else
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                    { sr: s }
                                                },
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                              { ss: s }
                                              =>
                                                {
                                                    let s_pr: (&[cbor_raw], &[cbor_raw]) =
                                                        s.split_at(cur_off_v);
                                                    let _s_prefix: &[cbor_raw] = s_pr.0;
                                                    let s_rest: &[cbor_raw] = s_pr.1;
                                                    let s_ms: (&[cbor_raw], &[cbor_raw]) =
                                                        s_rest.split_at(cur_n_v);
                                                    let s_middle: &[cbor_raw] = s_ms.0;
                                                    let _s_suffix: &[cbor_raw] = s_ms.1;
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                    { ss: s_middle }
                                                },
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                              { payload: pl, .. }
                                              =>
                                                {
                                                    let mut pn: [usize; 1] = [cur_off_v; 1usize];
                                                    let mut poffset: [usize; 1] = [0usize; 1usize];
                                                    let n1: usize = (&pn)[0];
                                                    let mut cond0: bool = n1 > 0usize;
                                                    while
                                                    cond0
                                                    {
                                                        let n10: usize = (&pn)[0];
                                                        let offset: usize = (&poffset)[0];
                                                        let offset·: usize =
                                                            jump_raw_data_item(pl, offset);
                                                        (&mut pn)[0] = n10.wrapping_sub(1usize);
                                                        (&mut poffset)[0] = offset·;
                                                        let n11: usize = (&pn)[0];
                                                        cond0 = n11 > 0usize
                                                    };
                                                    let pos: usize = (&poffset)[0];
                                                    let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                                    let _pl_prefix: &[u8] = pl_p.0;
                                                    let pl_suffix: &[u8] = pl_p.1;
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                    { count: cur_n_v, payload: pl_suffix }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          };
                                      let len: usize =
                                          base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                              bi·
                                          );
                                      (bi·,len)
                                  },
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append { .. } =>
                                  panic!("Pulse.Lib.Dv.unreachable"),
                                _ => panic!("Incomplete pattern matching")
                            };
                        let bi: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                            fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                res0
                            );
                        let chunk_len: usize =
                            snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                res0
                            );
                        match bi
                        {
                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                            { payload: pl_bi, .. }
                            =>
                              {
                                  let mut pn: [usize; 1] = [chunk_len; 1usize];
                                  let mut poffset: [usize; 1] = [0usize; 1usize];
                                  let n1: usize = (&pn)[0];
                                  let mut cond0: bool = n1 > 0usize;
                                  while
                                  cond0
                                  {
                                      let n10: usize = (&pn)[0];
                                      let offset: usize = (&poffset)[0];
                                      let offset·: usize = jump_raw_data_item(pl_bi, offset);
                                      (&mut pn)[0] = n10.wrapping_sub(1usize);
                                      (&mut poffset)[0] = offset·;
                                      let n11: usize = (&pn)[0];
                                      cond0 = n11 > 0usize
                                  };
                                  let byte_len: usize = (&poffset)[0];
                                  let remaining: usize = out[0];
                                  let chunk_res: bool =
                                      if byte_len <= remaining
                                      {
                                          out[0] = remaining.wrapping_sub(byte_len);
                                          true
                                      }
                                      else
                                      { false };
                                  let new_rem: usize = cur_rem.wrapping_sub(chunk_len);
                                  let new_node: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                                      match cur
                                      {
                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                          { _0: bi1 }
                                          =>
                                            {
                                                let
                                                bi·:
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                =
                                                    match bi1
                                                    {
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                        =>
                                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                        { sr: s }
                                                        =>
                                                          if new_rem == 0usize
                                                          {
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                          }
                                                          else
                                                          {
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                              { sr: s }
                                                          },
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                        { ss: s }
                                                        =>
                                                          {
                                                              let s_pr: (&[cbor_raw], &[cbor_raw]) =
                                                                  s.split_at(chunk_len);
                                                              let _s_prefix: &[cbor_raw] = s_pr.0;
                                                              let s_rest: &[cbor_raw] = s_pr.1;
                                                              let s_ms: (&[cbor_raw], &[cbor_raw]) =
                                                                  s_rest.split_at(new_rem);
                                                              let s_middle: &[cbor_raw] = s_ms.0;
                                                              let _s_suffix: &[cbor_raw] = s_ms.1;
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                              { ss: s_middle }
                                                          },
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                        { payload: pl, .. }
                                                        =>
                                                          {
                                                              let mut pn0: [usize; 1] =
                                                                  [chunk_len; 1usize];
                                                              let mut poffset0: [usize; 1] =
                                                                  [0usize; 1usize];
                                                              let n10: usize = (&pn0)[0];
                                                              let mut cond1: bool = n10 > 0usize;
                                                              while
                                                              cond1
                                                              {
                                                                  let n11: usize = (&pn0)[0];
                                                                  let offset: usize =
                                                                      (&poffset0)[0];
                                                                  let offset·: usize =
                                                                      jump_raw_data_item(pl, offset);
                                                                  (&mut pn0)[0] =
                                                                      n11.wrapping_sub(1usize);
                                                                  (&mut poffset0)[0] = offset·;
                                                                  let n12: usize = (&pn0)[0];
                                                                  cond1 = n12 > 0usize
                                                              };
                                                              let pos: usize = (&poffset0)[0];
                                                              let pl_p: (&[u8], &[u8]) =
                                                                  pl.split_at(pos);
                                                              let _pl_prefix: &[u8] = pl_p.0;
                                                              let pl_suffix: &[u8] = pl_p.1;
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                              { count: new_rem, payload: pl_suffix }
                                                          },
                                                        _ => panic!("Incomplete pattern matching")
                                                    };
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                { _0: bi· }
                                            },
                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                          { cb, ca, ob, before, oa, after }
                                          =>
                                            {
                                                let cb·_sz: usize =
                                                    append_n_before_sz(chunk_len, new_rem, cb);
                                                let ca·_sz: usize =
                                                    append_n_after_sz(chunk_len, new_rem, cb);
                                                let ob·_sz: usize =
                                                    append_off_before_sz(chunk_len, ob, cb);
                                                let oa·_sz: usize =
                                                    append_off_after_sz(chunk_len, oa, ca, cb);
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                {
                                                    cb: cb·_sz,
                                                    ca: ca·_sz,
                                                    ob: ob·_sz,
                                                    before,
                                                    oa: oa·_sz,
                                                    after
                                                }
                                            },
                                          _ => panic!("Incomplete pattern matching")
                                      };
                                  if chunk_res
                                  {
                                      (&mut p_node)[0] = new_node;
                                      (&mut p_remaining)[0] = new_rem
                                  }
                                  else
                                  {
                                      (&mut p_node)[0] = new_node;
                                      (&mut p_remaining)[0] = new_rem;
                                      (&mut p_result)[0] = false
                                  }
                              },
                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                            { ss: ss_bi }
                            =>
                              {
                                  let mut pres: [bool; 1] = [true; 1usize];
                                  let mut pi: [usize; 1] = [0usize; 1usize];
                                  let res2: bool = (&pres)[0];
                                  let i1: usize = (&pi)[0];
                                  let mut cond0: bool = res2 && i1 < chunk_len;
                                  while
                                  cond0
                                  {
                                      let i10: usize = (&pi)[0];
                                      let e: cbor_raw = ss_bi[i10];
                                      let x2·: cbor_raw = e;
                                      let res20: bool = siz·(x2·, out);
                                      if res20
                                      {
                                          let i·: usize = i10.wrapping_add(1usize);
                                          (&mut pi)[0] = i·
                                      }
                                      else
                                      { (&mut pres)[0] = false };
                                      let res21: bool = (&pres)[0];
                                      let i11: usize = (&pi)[0];
                                      cond0 = res21 && i11 < chunk_len
                                  };
                                  let chunk_res: bool = (&pres)[0];
                                  let new_rem: usize = cur_rem.wrapping_sub(chunk_len);
                                  let new_node: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                                      match cur
                                      {
                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                          { _0: bi1 }
                                          =>
                                            {
                                                let
                                                bi·:
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                =
                                                    match bi1
                                                    {
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                        =>
                                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                        { sr: s }
                                                        =>
                                                          if new_rem == 0usize
                                                          {
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                          }
                                                          else
                                                          {
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                              { sr: s }
                                                          },
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                        { ss: s }
                                                        =>
                                                          {
                                                              let s_pr: (&[cbor_raw], &[cbor_raw]) =
                                                                  s.split_at(chunk_len);
                                                              let _s_prefix: &[cbor_raw] = s_pr.0;
                                                              let s_rest: &[cbor_raw] = s_pr.1;
                                                              let s_ms: (&[cbor_raw], &[cbor_raw]) =
                                                                  s_rest.split_at(new_rem);
                                                              let s_middle: &[cbor_raw] = s_ms.0;
                                                              let _s_suffix: &[cbor_raw] = s_ms.1;
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                              { ss: s_middle }
                                                          },
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                        { payload: pl, .. }
                                                        =>
                                                          {
                                                              let mut pn: [usize; 1] =
                                                                  [chunk_len; 1usize];
                                                              let mut poffset: [usize; 1] =
                                                                  [0usize; 1usize];
                                                              let n1: usize = (&pn)[0];
                                                              let mut cond1: bool = n1 > 0usize;
                                                              while
                                                              cond1
                                                              {
                                                                  let n10: usize = (&pn)[0];
                                                                  let offset: usize = (&poffset)[0];
                                                                  let offset·: usize =
                                                                      jump_raw_data_item(pl, offset);
                                                                  (&mut pn)[0] =
                                                                      n10.wrapping_sub(1usize);
                                                                  (&mut poffset)[0] = offset·;
                                                                  let n11: usize = (&pn)[0];
                                                                  cond1 = n11 > 0usize
                                                              };
                                                              let pos: usize = (&poffset)[0];
                                                              let pl_p: (&[u8], &[u8]) =
                                                                  pl.split_at(pos);
                                                              let _pl_prefix: &[u8] = pl_p.0;
                                                              let pl_suffix: &[u8] = pl_p.1;
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                              { count: new_rem, payload: pl_suffix }
                                                          },
                                                        _ => panic!("Incomplete pattern matching")
                                                    };
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                { _0: bi· }
                                            },
                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                          { cb, ca, ob, before, oa, after }
                                          =>
                                            {
                                                let cb·_sz: usize =
                                                    append_n_before_sz(chunk_len, new_rem, cb);
                                                let ca·_sz: usize =
                                                    append_n_after_sz(chunk_len, new_rem, cb);
                                                let ob·_sz: usize =
                                                    append_off_before_sz(chunk_len, ob, cb);
                                                let oa·_sz: usize =
                                                    append_off_after_sz(chunk_len, oa, ca, cb);
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                {
                                                    cb: cb·_sz,
                                                    ca: ca·_sz,
                                                    ob: ob·_sz,
                                                    before,
                                                    oa: oa·_sz,
                                                    after
                                                }
                                            },
                                          _ => panic!("Incomplete pattern matching")
                                      };
                                  if chunk_res
                                  {
                                      (&mut p_node)[0] = new_node;
                                      (&mut p_remaining)[0] = new_rem
                                  }
                                  else
                                  {
                                      (&mut p_node)[0] = new_node;
                                      (&mut p_remaining)[0] = new_rem;
                                      (&mut p_result)[0] = false
                                  }
                              },
                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                            { sr: sr_bi }
                            =>
                              {
                                  let xv: cbor_raw = sr_bi[0];
                                  let x2·: cbor_raw = xv;
                                  let chunk_res: bool = siz·(x2·, out);
                                  let new_rem: usize = cur_rem.wrapping_sub(chunk_len);
                                  let new_node: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                                      match cur
                                      {
                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                          { _0: bi1 }
                                          =>
                                            {
                                                let
                                                bi·:
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                =
                                                    match bi1
                                                    {
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                        =>
                                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                        { sr: s }
                                                        =>
                                                          if new_rem == 0usize
                                                          {
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                          }
                                                          else
                                                          {
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                              { sr: s }
                                                          },
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                        { ss: s }
                                                        =>
                                                          {
                                                              let s_pr: (&[cbor_raw], &[cbor_raw]) =
                                                                  s.split_at(chunk_len);
                                                              let _s_prefix: &[cbor_raw] = s_pr.0;
                                                              let s_rest: &[cbor_raw] = s_pr.1;
                                                              let s_ms: (&[cbor_raw], &[cbor_raw]) =
                                                                  s_rest.split_at(new_rem);
                                                              let s_middle: &[cbor_raw] = s_ms.0;
                                                              let _s_suffix: &[cbor_raw] = s_ms.1;
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                              { ss: s_middle }
                                                          },
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                        { payload: pl, .. }
                                                        =>
                                                          {
                                                              let mut pn: [usize; 1] =
                                                                  [chunk_len; 1usize];
                                                              let mut poffset: [usize; 1] =
                                                                  [0usize; 1usize];
                                                              let n1: usize = (&pn)[0];
                                                              let mut cond0: bool = n1 > 0usize;
                                                              while
                                                              cond0
                                                              {
                                                                  let n10: usize = (&pn)[0];
                                                                  let offset: usize = (&poffset)[0];
                                                                  let offset·: usize =
                                                                      jump_raw_data_item(pl, offset);
                                                                  (&mut pn)[0] =
                                                                      n10.wrapping_sub(1usize);
                                                                  (&mut poffset)[0] = offset·;
                                                                  let n11: usize = (&pn)[0];
                                                                  cond0 = n11 > 0usize
                                                              };
                                                              let pos: usize = (&poffset)[0];
                                                              let pl_p: (&[u8], &[u8]) =
                                                                  pl.split_at(pos);
                                                              let _pl_prefix: &[u8] = pl_p.0;
                                                              let pl_suffix: &[u8] = pl_p.1;
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                              { count: new_rem, payload: pl_suffix }
                                                          },
                                                        _ => panic!("Incomplete pattern matching")
                                                    };
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                { _0: bi· }
                                            },
                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                          { cb, ca, ob, before, oa, after }
                                          =>
                                            {
                                                let cb·_sz: usize =
                                                    append_n_before_sz(chunk_len, new_rem, cb);
                                                let ca·_sz: usize =
                                                    append_n_after_sz(chunk_len, new_rem, cb);
                                                let ob·_sz: usize =
                                                    append_off_before_sz(chunk_len, ob, cb);
                                                let oa·_sz: usize =
                                                    append_off_after_sz(chunk_len, oa, ca, cb);
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                {
                                                    cb: cb·_sz,
                                                    ca: ca·_sz,
                                                    ob: ob·_sz,
                                                    before,
                                                    oa: oa·_sz,
                                                    after
                                                }
                                            },
                                          _ => panic!("Incomplete pattern matching")
                                      };
                                  if chunk_res
                                  {
                                      (&mut p_node)[0] = new_node;
                                      (&mut p_remaining)[0] = new_rem
                                  }
                                  else
                                  {
                                      (&mut p_node)[0] = new_node;
                                      (&mut p_remaining)[0] = new_rem;
                                      (&mut p_result)[0] = false
                                  }
                              },
                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty => (),
                            _ => panic!("Incomplete pattern matching")
                        };
                        let res2: bool = (&p_result)[0];
                        let rem0: usize = (&p_remaining)[0];
                        cond = res2 && rem0 > 0usize
                    };
                    (&p_result)[0]
                }
            }
            else
            {
                let b1: initial_byte_t = xh1.fst;
                if b1.major_type == cbor_major_type_map
                {
                    let
                    arr:
                    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                    =
                        cbor_raw_get_map(x·);
                    let n: usize = argument_as_uint64(xh1.fst, xh1.snd) as usize;
                    if n == 0usize
                    { true }
                    else
                    {
                        let
                        mut
                        p_node:
                        [mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;
                        1]
                        =
                            [arr; 1usize];
                        let mut p_remaining: [usize; 1] = [n; 1usize];
                        let mut p_result: [bool; 1] = [true; 1usize];
                        let res: bool = (&p_result)[0];
                        let rem: usize = (&p_remaining)[0];
                        let mut cond: bool = res && rem > 0usize;
                        while
                        cond
                        {
                            let
                            cur:
                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                            =
                                (&p_node)[0];
                            let cur_rem: usize = (&p_remaining)[0];
                            let
                            mut
                            r_node:
                            [mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;
                            1]
                            =
                                [cur; 1usize];
                            let mut r_off: [usize; 1] = [0usize; 1usize];
                            let mut r_n: [usize; 1] = [cur_rem; 1usize];
                            let mut pcontinue: [bool; 1] =
                                [!
                                    uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                        cur
                                    );
                                    1usize];
                            while
                            (&pcontinue)[0]
                            {
                                let
                                node:
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                =
                                    (&r_node)[0];
                                let cur_off_v: usize = (&r_off)[0];
                                let cur_n_v: usize = (&r_n)[0];
                                match node
                                {
                                    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                    { cb, ca, ob, before, oa, after }
                                    =>
                                      {
                                          let child_n_before: usize =
                                              append_n_before_sz(cur_off_v, cur_n_v, cb);
                                          if child_n_before > 0usize
                                          {
                                              let child_off_sz: usize =
                                                  append_off_before_sz(cur_off_v, ob, cb);
                                              let
                                              ib:
                                              mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                              =
                                                  before[0];
                                              (&mut r_node)[0] = ib;
                                              (&mut r_off)[0] = child_off_sz;
                                              (&mut r_n)[0] = child_n_before;
                                              (&mut pcontinue)[0] =
                                                  !
                                                  uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                      ib
                                                  )
                                          }
                                          else
                                          {
                                              let child_off_sz: usize =
                                                  append_off_after_sz(cur_off_v, oa, ca, cb);
                                              let child_n_sz: usize =
                                                  append_n_after_sz(cur_off_v, cur_n_v, cb);
                                              let
                                              ia:
                                              mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                              =
                                                  after[0];
                                              (&mut r_node)[0] = ia;
                                              (&mut r_off)[0] = child_off_sz;
                                              (&mut r_n)[0] = child_n_sz;
                                              (&mut pcontinue)[0] =
                                                  !
                                                  uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                      ia
                                                  )
                                          }
                                      },
                                    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                    { .. }
                                    => (),
                                    _ => panic!("Incomplete pattern matching")
                                }
                            };
                            let
                            node:
                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                            =
                                (&r_node)[0];
                            let cur_off_v: usize = (&r_off)[0];
                            let cur_n_v: usize = (&r_n)[0];
                            let
                            res0:
                            (base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                            usize)
                            =
                                match node
                                {
                                    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                    { _0: bi }
                                    =>
                                      {
                                          let
                                          bi·:
                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                          =
                                              match bi
                                              {
                                                  base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                  =>
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                  base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                  { sr: s }
                                                  =>
                                                    if cur_n_v == 0usize
                                                    {
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                    }
                                                    else
                                                    {
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                        { sr: s }
                                                    },
                                                  base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                  { ss: s }
                                                  =>
                                                    {
                                                        let
                                                        s_pr:
                                                        (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                        &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                        =
                                                            s.split_at(cur_off_v);
                                                        let
                                                        _s_prefix:
                                                        &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                        =
                                                            s_pr.0;
                                                        let
                                                        s_rest:
                                                        &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                        =
                                                            s_pr.1;
                                                        let
                                                        s_ms:
                                                        (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                        &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                        =
                                                            s_rest.split_at(cur_n_v);
                                                        let
                                                        s_middle:
                                                        &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                        =
                                                            s_ms.0;
                                                        let
                                                        _s_suffix:
                                                        &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                        =
                                                            s_ms.1;
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                        { ss: s_middle }
                                                    },
                                                  base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                  { payload: pl, .. }
                                                  =>
                                                    {
                                                        let mut pn: [usize; 1] =
                                                            [cur_off_v; 1usize];
                                                        let mut poffset: [usize; 1] =
                                                            [0usize; 1usize];
                                                        let n1: usize = (&pn)[0];
                                                        let mut cond0: bool = n1 > 0usize;
                                                        while
                                                        cond0
                                                        {
                                                            let n10: usize = (&pn)[0];
                                                            let offset: usize = (&poffset)[0];
                                                            let off1: usize =
                                                                jump_raw_data_item(pl, offset);
                                                            let offset·: usize =
                                                                jump_raw_data_item(pl, off1);
                                                            (&mut pn)[0] = n10.wrapping_sub(1usize);
                                                            (&mut poffset)[0] = offset·;
                                                            let n11: usize = (&pn)[0];
                                                            cond0 = n11 > 0usize
                                                        };
                                                        let pos: usize = (&poffset)[0];
                                                        let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                                        let _pl_prefix: &[u8] = pl_p.0;
                                                        let pl_suffix: &[u8] = pl_p.1;
                                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                        { count: cur_n_v, payload: pl_suffix }
                                                    },
                                                  _ => panic!("Incomplete pattern matching")
                                              };
                                          let len: usize =
                                              base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                  bi·
                                              );
                                          (bi·,len)
                                      },
                                    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                    { .. }
                                    => panic!("Pulse.Lib.Dv.unreachable"),
                                    _ => panic!("Incomplete pattern matching")
                                };
                            let
                            bi:
                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                            =
                                fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                    res0
                                );
                            let chunk_len: usize =
                                snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                    res0
                                );
                            match bi
                            {
                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                { payload: pl_bi, .. }
                                =>
                                  {
                                      let mut pn: [usize; 1] = [chunk_len; 1usize];
                                      let mut poffset: [usize; 1] = [0usize; 1usize];
                                      let n1: usize = (&pn)[0];
                                      let mut cond0: bool = n1 > 0usize;
                                      while
                                      cond0
                                      {
                                          let n10: usize = (&pn)[0];
                                          let offset: usize = (&poffset)[0];
                                          let off1: usize = jump_raw_data_item(pl_bi, offset);
                                          let offset·: usize = jump_raw_data_item(pl_bi, off1);
                                          (&mut pn)[0] = n10.wrapping_sub(1usize);
                                          (&mut poffset)[0] = offset·;
                                          let n11: usize = (&pn)[0];
                                          cond0 = n11 > 0usize
                                      };
                                      let byte_len: usize = (&poffset)[0];
                                      let remaining: usize = out[0];
                                      let chunk_res: bool =
                                          if byte_len <= remaining
                                          {
                                              out[0] = remaining.wrapping_sub(byte_len);
                                              true
                                          }
                                          else
                                          { false };
                                      let new_rem: usize = cur_rem.wrapping_sub(chunk_len);
                                      let
                                      new_node:
                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                      =
                                          match cur
                                          {
                                              mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                              { _0: bi1 }
                                              =>
                                                {
                                                    let
                                                    bi·:
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                    =
                                                        match bi1
                                                        {
                                                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                            =>
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                            { sr: s }
                                                            =>
                                                              if new_rem == 0usize
                                                              {
                                                                  base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                              }
                                                              else
                                                              {
                                                                  base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                                  { sr: s }
                                                              },
                                                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                            { ss: s }
                                                            =>
                                                              {
                                                                  let
                                                                  s_pr:
                                                                  (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                                  &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                                  =
                                                                      s.split_at(chunk_len);
                                                                  let
                                                                  _s_prefix:
                                                                  &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                  =
                                                                      s_pr.0;
                                                                  let
                                                                  s_rest:
                                                                  &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                  =
                                                                      s_pr.1;
                                                                  let
                                                                  s_ms:
                                                                  (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                                  &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                                  =
                                                                      s_rest.split_at(new_rem);
                                                                  let
                                                                  s_middle:
                                                                  &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                  =
                                                                      s_ms.0;
                                                                  let
                                                                  _s_suffix:
                                                                  &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                  =
                                                                      s_ms.1;
                                                                  base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                                  { ss: s_middle }
                                                              },
                                                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                            { payload: pl, .. }
                                                            =>
                                                              {
                                                                  let mut pn0: [usize; 1] =
                                                                      [chunk_len; 1usize];
                                                                  let mut poffset0: [usize; 1] =
                                                                      [0usize; 1usize];
                                                                  let n10: usize = (&pn0)[0];
                                                                  let mut cond1: bool =
                                                                      n10 > 0usize;
                                                                  while
                                                                  cond1
                                                                  {
                                                                      let n11: usize = (&pn0)[0];
                                                                      let offset: usize =
                                                                          (&poffset0)[0];
                                                                      let off1: usize =
                                                                          jump_raw_data_item(
                                                                              pl,
                                                                              offset
                                                                          );
                                                                      let offset·: usize =
                                                                          jump_raw_data_item(
                                                                              pl,
                                                                              off1
                                                                          );
                                                                      (&mut pn0)[0] =
                                                                          n11.wrapping_sub(1usize);
                                                                      (&mut poffset0)[0] = offset·;
                                                                      let n12: usize = (&pn0)[0];
                                                                      cond1 = n12 > 0usize
                                                                  };
                                                                  let pos: usize = (&poffset0)[0];
                                                                  let pl_p: (&[u8], &[u8]) =
                                                                      pl.split_at(pos);
                                                                  let _pl_prefix: &[u8] = pl_p.0;
                                                                  let pl_suffix: &[u8] = pl_p.1;
                                                                  base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                                  {
                                                                      count: new_rem,
                                                                      payload: pl_suffix
                                                                  }
                                                              },
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        };
                                                    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                    { _0: bi· }
                                                },
                                              mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                              { cb, ca, ob, before, oa, after }
                                              =>
                                                {
                                                    let cb·_sz: usize =
                                                        append_n_before_sz(chunk_len, new_rem, cb);
                                                    let ca·_sz: usize =
                                                        append_n_after_sz(chunk_len, new_rem, cb);
                                                    let ob·_sz: usize =
                                                        append_off_before_sz(chunk_len, ob, cb);
                                                    let oa·_sz: usize =
                                                        append_off_after_sz(chunk_len, oa, ca, cb);
                                                    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                    {
                                                        cb: cb·_sz,
                                                        ca: ca·_sz,
                                                        ob: ob·_sz,
                                                        before,
                                                        oa: oa·_sz,
                                                        after
                                                    }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          };
                                      if chunk_res
                                      {
                                          (&mut p_node)[0] = new_node;
                                          (&mut p_remaining)[0] = new_rem
                                      }
                                      else
                                      {
                                          (&mut p_node)[0] = new_node;
                                          (&mut p_remaining)[0] = new_rem;
                                          (&mut p_result)[0] = false
                                      }
                                  },
                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                { ss: ss_bi }
                                =>
                                  {
                                      let mut pres: [bool; 1] = [true; 1usize];
                                      let mut pi: [usize; 1] = [0usize; 1usize];
                                      let res2: bool = (&pres)[0];
                                      let i1: usize = (&pi)[0];
                                      let mut cond0: bool = res2 && i1 < chunk_len;
                                      while
                                      cond0
                                      {
                                          let i10: usize = (&pi)[0];
                                          let
                                          e: cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                          =
                                              ss_bi[i10];
                                          let x11: cbor_raw = e.cbor_map_entry_key;
                                          let res11: bool = siz·(x11, out);
                                          let res20: bool =
                                              if res11
                                              {
                                                  let x2: cbor_raw = e.cbor_map_entry_value;
                                                  siz·(x2, out)
                                              }
                                              else
                                              { false };
                                          if res20
                                          {
                                              let i·: usize = i10.wrapping_add(1usize);
                                              (&mut pi)[0] = i·
                                          }
                                          else
                                          { (&mut pres)[0] = false };
                                          let res21: bool = (&pres)[0];
                                          let i11: usize = (&pi)[0];
                                          cond0 = res21 && i11 < chunk_len
                                      };
                                      let chunk_res: bool = (&pres)[0];
                                      let new_rem: usize = cur_rem.wrapping_sub(chunk_len);
                                      let
                                      new_node:
                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                      =
                                          match cur
                                          {
                                              mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                              { _0: bi1 }
                                              =>
                                                {
                                                    let
                                                    bi·:
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                    =
                                                        match bi1
                                                        {
                                                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                            =>
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                            { sr: s }
                                                            =>
                                                              if new_rem == 0usize
                                                              {
                                                                  base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                              }
                                                              else
                                                              {
                                                                  base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                                  { sr: s }
                                                              },
                                                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                            { ss: s }
                                                            =>
                                                              {
                                                                  let
                                                                  s_pr:
                                                                  (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                                  &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                                  =
                                                                      s.split_at(chunk_len);
                                                                  let
                                                                  _s_prefix:
                                                                  &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                  =
                                                                      s_pr.0;
                                                                  let
                                                                  s_rest:
                                                                  &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                  =
                                                                      s_pr.1;
                                                                  let
                                                                  s_ms:
                                                                  (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                                  &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                                  =
                                                                      s_rest.split_at(new_rem);
                                                                  let
                                                                  s_middle:
                                                                  &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                  =
                                                                      s_ms.0;
                                                                  let
                                                                  _s_suffix:
                                                                  &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                  =
                                                                      s_ms.1;
                                                                  base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                                  { ss: s_middle }
                                                              },
                                                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                            { payload: pl, .. }
                                                            =>
                                                              {
                                                                  let mut pn: [usize; 1] =
                                                                      [chunk_len; 1usize];
                                                                  let mut poffset: [usize; 1] =
                                                                      [0usize; 1usize];
                                                                  let n1: usize = (&pn)[0];
                                                                  let mut cond1: bool = n1 > 0usize;
                                                                  while
                                                                  cond1
                                                                  {
                                                                      let n10: usize = (&pn)[0];
                                                                      let offset: usize =
                                                                          (&poffset)[0];
                                                                      let off1: usize =
                                                                          jump_raw_data_item(
                                                                              pl,
                                                                              offset
                                                                          );
                                                                      let offset·: usize =
                                                                          jump_raw_data_item(
                                                                              pl,
                                                                              off1
                                                                          );
                                                                      (&mut pn)[0] =
                                                                          n10.wrapping_sub(1usize);
                                                                      (&mut poffset)[0] = offset·;
                                                                      let n11: usize = (&pn)[0];
                                                                      cond1 = n11 > 0usize
                                                                  };
                                                                  let pos: usize = (&poffset)[0];
                                                                  let pl_p: (&[u8], &[u8]) =
                                                                      pl.split_at(pos);
                                                                  let _pl_prefix: &[u8] = pl_p.0;
                                                                  let pl_suffix: &[u8] = pl_p.1;
                                                                  base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                                  {
                                                                      count: new_rem,
                                                                      payload: pl_suffix
                                                                  }
                                                              },
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        };
                                                    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                    { _0: bi· }
                                                },
                                              mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                              { cb, ca, ob, before, oa, after }
                                              =>
                                                {
                                                    let cb·_sz: usize =
                                                        append_n_before_sz(chunk_len, new_rem, cb);
                                                    let ca·_sz: usize =
                                                        append_n_after_sz(chunk_len, new_rem, cb);
                                                    let ob·_sz: usize =
                                                        append_off_before_sz(chunk_len, ob, cb);
                                                    let oa·_sz: usize =
                                                        append_off_after_sz(chunk_len, oa, ca, cb);
                                                    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                    {
                                                        cb: cb·_sz,
                                                        ca: ca·_sz,
                                                        ob: ob·_sz,
                                                        before,
                                                        oa: oa·_sz,
                                                        after
                                                    }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          };
                                      if chunk_res
                                      {
                                          (&mut p_node)[0] = new_node;
                                          (&mut p_remaining)[0] = new_rem
                                      }
                                      else
                                      {
                                          (&mut p_node)[0] = new_node;
                                          (&mut p_remaining)[0] = new_rem;
                                          (&mut p_result)[0] = false
                                      }
                                  },
                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                { sr: sr_bi }
                                =>
                                  {
                                      let
                                      xv: cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                      =
                                          sr_bi[0];
                                      let x11: cbor_raw = xv.cbor_map_entry_key;
                                      let res11: bool = siz·(x11, out);
                                      let chunk_res: bool =
                                          if res11
                                          {
                                              let x2: cbor_raw = xv.cbor_map_entry_value;
                                              siz·(x2, out)
                                          }
                                          else
                                          { false };
                                      let new_rem: usize = cur_rem.wrapping_sub(chunk_len);
                                      let
                                      new_node:
                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                      =
                                          match cur
                                          {
                                              mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                              { _0: bi1 }
                                              =>
                                                {
                                                    let
                                                    bi·:
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                    =
                                                        match bi1
                                                        {
                                                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                            =>
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                            { sr: s }
                                                            =>
                                                              if new_rem == 0usize
                                                              {
                                                                  base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                              }
                                                              else
                                                              {
                                                                  base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                                  { sr: s }
                                                              },
                                                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                            { ss: s }
                                                            =>
                                                              {
                                                                  let
                                                                  s_pr:
                                                                  (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                                  &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                                  =
                                                                      s.split_at(chunk_len);
                                                                  let
                                                                  _s_prefix:
                                                                  &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                  =
                                                                      s_pr.0;
                                                                  let
                                                                  s_rest:
                                                                  &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                  =
                                                                      s_pr.1;
                                                                  let
                                                                  s_ms:
                                                                  (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                                  &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                                  =
                                                                      s_rest.split_at(new_rem);
                                                                  let
                                                                  s_middle:
                                                                  &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                  =
                                                                      s_ms.0;
                                                                  let
                                                                  _s_suffix:
                                                                  &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                  =
                                                                      s_ms.1;
                                                                  base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                                  { ss: s_middle }
                                                              },
                                                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                            { payload: pl, .. }
                                                            =>
                                                              {
                                                                  let mut pn: [usize; 1] =
                                                                      [chunk_len; 1usize];
                                                                  let mut poffset: [usize; 1] =
                                                                      [0usize; 1usize];
                                                                  let n1: usize = (&pn)[0];
                                                                  let mut cond0: bool = n1 > 0usize;
                                                                  while
                                                                  cond0
                                                                  {
                                                                      let n10: usize = (&pn)[0];
                                                                      let offset: usize =
                                                                          (&poffset)[0];
                                                                      let off1: usize =
                                                                          jump_raw_data_item(
                                                                              pl,
                                                                              offset
                                                                          );
                                                                      let offset·: usize =
                                                                          jump_raw_data_item(
                                                                              pl,
                                                                              off1
                                                                          );
                                                                      (&mut pn)[0] =
                                                                          n10.wrapping_sub(1usize);
                                                                      (&mut poffset)[0] = offset·;
                                                                      let n11: usize = (&pn)[0];
                                                                      cond0 = n11 > 0usize
                                                                  };
                                                                  let pos: usize = (&poffset)[0];
                                                                  let pl_p: (&[u8], &[u8]) =
                                                                      pl.split_at(pos);
                                                                  let _pl_prefix: &[u8] = pl_p.0;
                                                                  let pl_suffix: &[u8] = pl_p.1;
                                                                  base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                                  {
                                                                      count: new_rem,
                                                                      payload: pl_suffix
                                                                  }
                                                              },
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        };
                                                    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                    { _0: bi· }
                                                },
                                              mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                              { cb, ca, ob, before, oa, after }
                                              =>
                                                {
                                                    let cb·_sz: usize =
                                                        append_n_before_sz(chunk_len, new_rem, cb);
                                                    let ca·_sz: usize =
                                                        append_n_after_sz(chunk_len, new_rem, cb);
                                                    let ob·_sz: usize =
                                                        append_off_before_sz(chunk_len, ob, cb);
                                                    let oa·_sz: usize =
                                                        append_off_after_sz(chunk_len, oa, ca, cb);
                                                    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                    {
                                                        cb: cb·_sz,
                                                        ca: ca·_sz,
                                                        ob: ob·_sz,
                                                        before,
                                                        oa: oa·_sz,
                                                        after
                                                    }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          };
                                      if chunk_res
                                      {
                                          (&mut p_node)[0] = new_node;
                                          (&mut p_remaining)[0] = new_rem
                                      }
                                      else
                                      {
                                          (&mut p_node)[0] = new_node;
                                          (&mut p_remaining)[0] = new_rem;
                                          (&mut p_result)[0] = false
                                      }
                                  },
                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                => (),
                                _ => panic!("Incomplete pattern matching")
                            };
                            let res2: bool = (&p_result)[0];
                            let rem0: usize = (&p_remaining)[0];
                            cond = res2 && rem0 > 0usize
                        };
                        (&p_result)[0]
                    }
                }
                else
                {
                    let b2: initial_byte_t = xh1.fst;
                    if b2.major_type == cbor_major_type_tagged
                    {
                        let payload: cbor_raw = cbor_raw_get_tagged_payload(x·);
                        let x2·: cbor_raw = payload;
                        siz·(x2·, out)
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
    if fits { write_header(h, output, 0usize) } else { 0usize }
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

fn cbor_raw_simple_value(x: cbor_raw) -> option__uint8_t
{
    match x
    { cbor_raw::CBOR_Case_Simple { v } => option__uint8_t::Some { v }, _ => option__uint8_t::None }
}

pub(crate) fn cbor_raw_read_simple_value(x: cbor_raw) -> u8
{
    let x0: option__uint8_t = cbor_raw_simple_value(x);
    match x0 { option__uint8_t::Some { v } => v, _ => panic!("Incomplete pattern matching") }
}

#[derive(PartialEq, Clone, Copy)]
enum option__uint64_t
{
    None,
    Some { v: u64 }
}

fn cbor_raw_int64_value(x: cbor_raw) -> option__uint64_t
{
    match x
    {
        cbor_raw::CBOR_Case_Int { v } => option__uint64_t::Some { v: v.cbor_int_value },
        _ => option__uint64_t::None
    }
}

pub(crate) fn cbor_raw_read_int64_value(x: cbor_raw) -> u64
{
    let x0: option__uint64_t = cbor_raw_int64_value(x);
    match x0 { option__uint64_t::Some { v } => v, _ => panic!("Incomplete pattern matching") }
}

fn cbor_raw_tagged_tag(x: cbor_raw) -> option__uint64_t
{
    match x
    {
        cbor_raw::CBOR_Case_Tagged { v } => option__uint64_t::Some { v: v.cbor_tagged_tag.value },
        cbor_raw::CBOR_Case_Tagged_Serialized { v } =>
          option__uint64_t::Some { v: v.cbor_tagged_serialized_tag.value },
        _ => option__uint64_t::None
    }
}

pub(crate) fn cbor_raw_read_tagged_tag(x: cbor_raw) -> u64
{
    let x0: option__uint64_t = cbor_raw_tagged_tag(x);
    match x0 { option__uint64_t::Some { v } => v, _ => panic!("Incomplete pattern matching") }
}

fn cbor_raw_array_length(x: cbor_raw) -> option__uint64_t
{
    match x
    {
        cbor_raw::CBOR_Case_Array { v } =>
          option__uint64_t::Some
          { v: mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(v.cbor_array_ptr) as u64 },
        _ => option__uint64_t::None
    }
}

pub(crate) fn cbor_raw_read_array_length(x: cbor_raw) -> u64
{
    let x0: option__uint64_t = cbor_raw_array_length(x);
    match x0 { option__uint64_t::Some { v } => v, _ => panic!("Incomplete pattern matching") }
}

fn cbor_raw_map_length(x: cbor_raw) -> option__uint64_t
{
    match x
    {
        cbor_raw::CBOR_Case_Map { v } =>
          option__uint64_t::Some
          {
              v:
              mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                  v.cbor_map_ptr
              )
              as
              u64
          },
        _ => option__uint64_t::None
    }
}

pub(crate) fn cbor_raw_read_map_length(x: cbor_raw) -> u64
{
    let x0: option__uint64_t = cbor_raw_map_length(x);
    match x0 { option__uint64_t::Some { v } => v, _ => panic!("Incomplete pattern matching") }
}

fn uint64_compare(x1: u64, x2: u64) -> i16
{ if x1 < x2 { -1i16 } else if x1 > x2 { 1i16 } else { 0i16 } }

fn impl_raw_uint64_compare(x1: raw_uint64, x2: raw_uint64) -> i16
{
    let c: i16 = impl_uint8_compare(x1.size, x2.size);
    if c == 0i16 { uint64_compare(x1.value, x2.value) } else { c }
}

fn cbor_raw_int_raw_uint64(x: cbor_raw) -> raw_uint64
{
    match x
    {
        cbor_raw::CBOR_Case_Int { v } =>
          raw_uint64 { size: v.cbor_int_size, value: v.cbor_int_value },
        _ => raw_uint64 { size: 0u8, value: 0u64 }
    }
}

fn cbor_raw_string_len(x: cbor_raw) -> raw_uint64
{
    match x
    {
        cbor_raw::CBOR_Case_String { v } =>
          raw_uint64 { size: v.cbor_string_size, value: (v.cbor_string_ptr).len() as u64 },
        _ => raw_uint64 { size: 0u8, value: 0u64 }
    }
}

fn cbor_raw_tag_raw_uint64(x: cbor_raw) -> raw_uint64
{
    match x
    {
        cbor_raw::CBOR_Case_Tagged { v } => v.cbor_tagged_tag,
        cbor_raw::CBOR_Case_Tagged_Serialized { v } => v.cbor_tagged_serialized_tag,
        _ => raw_uint64 { size: 0u8, value: 0u64 }
    }
}

fn cbor_raw_array_raw_uint64(x: cbor_raw) -> raw_uint64
{
    match x
    {
        cbor_raw::CBOR_Case_Array { v } =>
          raw_uint64
          {
              size: v.cbor_array_length_size,
              value:
              mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(v.cbor_array_ptr) as u64
          },
        _ => raw_uint64 { size: 0u8, value: 0u64 }
    }
}

fn cbor_raw_map_raw_uint64(x: cbor_raw) -> raw_uint64
{
    match x
    {
        cbor_raw::CBOR_Case_Map { v } =>
          raw_uint64
          {
              size: v.cbor_map_length_size,
              value:
              mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                  v.cbor_map_ptr
              )
              as
              u64
          },
        _ => raw_uint64 { size: 0u8, value: 0u64 }
    }
}

fn byte_compare_pts_to_parsed_data_item(s1: &[u8], s2: &[u8]) -> i16
{ lex_compare_bytes(s1, s2) }

fn fst__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>(
    x: (cbor_raw <'a>, cbor_raw <'a>)
) ->
    cbor_raw
    <'a>
{
    let _1: cbor_raw = x.0;
    let __2: cbor_raw = x.1;
    _1
}

fn snd__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>(
    x: (cbor_raw <'a>, cbor_raw <'a>)
) ->
    cbor_raw
    <'a>
{
    let __1: cbor_raw = x.0;
    let _2: cbor_raw = x.1;
    _2
}

#[derive(PartialEq, Clone, Copy)]
pub struct iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>
{
    pub before: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>,
    pub after: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>
}

#[derive(PartialEq, Clone, Copy)]
pub struct
iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
<'a>
{
    pub before:
    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>,
    pub after:
    mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
    <'a>
}

#[derive(PartialEq, Clone, Copy)]
pub(crate) enum
elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
<'a>
{
    EElement { _0: cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a> },
    ESerialized { _0: &'a [u8] }
}

pub(crate) fn impl_cbor_compare_fuel(x1: cbor_raw, x2: cbor_raw) -> i16
{
    let ty1: u8 = cbor_raw_get_major_type_aux(x1);
    let ty2: u8 = cbor_raw_get_major_type_aux(x2);
    let c: i16 = impl_uint8_compare(ty1, ty2);
    if c == 0i16
    {
        if ty1 == cbor_major_type_uint64 || ty1 == cbor_major_type_neg_int64
        {
            let ru1: raw_uint64 = cbor_raw_int_raw_uint64(x1);
            let ru2: raw_uint64 = cbor_raw_int_raw_uint64(x2);
            impl_raw_uint64_compare(ru1, ru2)
        }
        else if ty1 == cbor_major_type_byte_string || ty1 == cbor_major_type_text_string
        {
            let len1: raw_uint64 = cbor_raw_string_len(x1);
            let len2: raw_uint64 = cbor_raw_string_len(x2);
            let cl: i16 = impl_raw_uint64_compare(len1, len2);
            if cl == 0i16
            {
                let s1: &[u8] = cbor_raw_get_string_aux(x1);
                let s2: &[u8] = cbor_raw_get_string_aux(x2);
                lex_compare_bytes(s1, s2)
            }
            else
            { cl }
        }
        else if ty1 == cbor_major_type_tagged
        {
            let tag1: raw_uint64 = cbor_raw_tag_raw_uint64(x1);
            let tag2: raw_uint64 = cbor_raw_tag_raw_uint64(x2);
            let ct: i16 = impl_raw_uint64_compare(tag1, tag2);
            if ct == 0i16
            {
                let e1: elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                    cbor_raw_get_tagged_payload_aux_eos(x1);
                let e2: elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                    cbor_raw_get_tagged_payload_aux_eos(x2);
                match e1
                {
                    elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::EElement
                    { _0: xx1 }
                    =>
                      match e2
                      {
                          elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::EElement
                          { _0: xx2 }
                          => impl_cbor_compare_fuel(xx1, xx2),
                          elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::ESerialized
                          { _0: s2 }
                          =>
                            {
                                let xx2: cbor_raw = cbor_raw_read_fuel(s2);
                                impl_cbor_compare_fuel(xx1, xx2)
                            },
                          _ => panic!("Incomplete pattern matching")
                      },
                    elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::ESerialized
                    { _0: s1 }
                    =>
                      match e2
                      {
                          elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::EElement
                          { _0: xx2 }
                          =>
                            {
                                let xx1: cbor_raw = cbor_raw_read_fuel(s1);
                                impl_cbor_compare_fuel(xx1, xx2)
                            },
                          elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::ESerialized
                          { _0: s2 }
                          =>
                            {
                                let off: usize = jump_raw_data_item(s1, 0usize);
                                let s·: (&[u8], &[u8]) = s1.split_at(off);
                                let _letpattern: (&[u8], &[u8]) =
                                    {
                                        let s11: &[u8] = s·.0;
                                        let s21: &[u8] = s·.1;
                                        (s11,s21)
                                    };
                                let ex1: &[u8] =
                                    {
                                        let exact: &[u8] = _letpattern.0;
                                        let _rest: &[u8] = _letpattern.1;
                                        exact
                                    };
                                let off0: usize = jump_raw_data_item(s2, 0usize);
                                let s·0: (&[u8], &[u8]) = s2.split_at(off0);
                                let _letpattern0: (&[u8], &[u8]) =
                                    {
                                        let s11: &[u8] = s·0.0;
                                        let s21: &[u8] = s·0.1;
                                        (s11,s21)
                                    };
                                let ex2: &[u8] =
                                    {
                                        let exact: &[u8] = _letpattern0.0;
                                        let _rest: &[u8] = _letpattern0.1;
                                        exact
                                    };
                                lex_compare_bytes(ex1, ex2)
                            },
                          _ => panic!("Incomplete pattern matching")
                      },
                    _ => panic!("Incomplete pattern matching")
                }
            }
            else
            { ct }
        }
        else if ty1 == cbor_major_type_array
        {
            let len1: raw_uint64 = cbor_raw_array_raw_uint64(x1);
            let len2: raw_uint64 = cbor_raw_array_raw_uint64(x2);
            let cl: i16 = impl_raw_uint64_compare(len1, len2);
            if cl == 0i16
            {
                let len_sz: usize = len1.value as usize;
                let ar_ml1: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                    cbor_raw_get_array_aux(x1);
                let ar_ml2: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                    cbor_raw_get_array_aux(x2);
                let total_sz: usize =
                    mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ar_ml1);
                let it1_init: iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                    if total_sz == 0usize
                    {
                        iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                        {
                            before: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                            after:
                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                            { _0: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty }
                        }
                    }
                    else
                    {
                        let mut r_node: [mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw; 1] =
                            [ar_ml1; 1usize];
                        let mut r_off: [usize; 1] = [0usize; 1usize];
                        let mut r_n: [usize; 1] = [total_sz; 1usize];
                        let mut pcontinue: [bool; 1] =
                            [! uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ar_ml1); 1usize];
                        while
                        (&pcontinue)[0]
                        {
                            let node: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                                (&r_node)[0];
                            let cur_off_v: usize = (&r_off)[0];
                            let cur_n_v: usize = (&r_n)[0];
                            match node
                            {
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                { cb, ca, ob, before, oa, after }
                                =>
                                  {
                                      let child_n_before: usize =
                                          append_n_before_sz(cur_off_v, cur_n_v, cb);
                                      if child_n_before > 0usize
                                      {
                                          let child_off_sz: usize =
                                              append_off_before_sz(cur_off_v, ob, cb);
                                          let
                                          ib: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                          =
                                              before[0];
                                          (&mut r_node)[0] = ib;
                                          (&mut r_off)[0] = child_off_sz;
                                          (&mut r_n)[0] = child_n_before;
                                          (&mut pcontinue)[0] =
                                              !
                                              uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                  ib
                                              )
                                      }
                                      else
                                      {
                                          let child_off_sz: usize =
                                              append_off_after_sz(cur_off_v, oa, ca, cb);
                                          let child_n_sz: usize =
                                              append_n_after_sz(cur_off_v, cur_n_v, cb);
                                          let
                                          ia: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                          =
                                              after[0];
                                          (&mut r_node)[0] = ia;
                                          (&mut r_off)[0] = child_off_sz;
                                          (&mut r_n)[0] = child_n_sz;
                                          (&mut pcontinue)[0] =
                                              !
                                              uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                  ia
                                              )
                                      }
                                  },
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base { .. } =>
                                  (),
                                _ => panic!("Incomplete pattern matching")
                            }
                        };
                        let node: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw = (&r_node)[0];
                        let cur_off_v: usize = (&r_off)[0];
                        let cur_n_v: usize = (&r_n)[0];
                        let res: (base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw, usize) =
                            match node
                            {
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                { _0: bi }
                                =>
                                  {
                                      let
                                      bi·: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                      =
                                          match bi
                                          {
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                              =>
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                              { sr: s }
                                              =>
                                                if cur_n_v == 0usize
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                }
                                                else
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                    { sr: s }
                                                },
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                              { ss: s }
                                              =>
                                                {
                                                    let s_pr: (&[cbor_raw], &[cbor_raw]) =
                                                        s.split_at(cur_off_v);
                                                    let _s_prefix: &[cbor_raw] = s_pr.0;
                                                    let s_rest: &[cbor_raw] = s_pr.1;
                                                    let s_ms: (&[cbor_raw], &[cbor_raw]) =
                                                        s_rest.split_at(cur_n_v);
                                                    let s_middle: &[cbor_raw] = s_ms.0;
                                                    let _s_suffix: &[cbor_raw] = s_ms.1;
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                    { ss: s_middle }
                                                },
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                              { payload: pl, .. }
                                              =>
                                                {
                                                    let mut pn: [usize; 1] = [cur_off_v; 1usize];
                                                    let mut poffset: [usize; 1] = [0usize; 1usize];
                                                    let n1: usize = (&pn)[0];
                                                    let mut cond: bool = n1 > 0usize;
                                                    while
                                                    cond
                                                    {
                                                        let n10: usize = (&pn)[0];
                                                        let offset: usize = (&poffset)[0];
                                                        let offset·: usize =
                                                            jump_raw_data_item(pl, offset);
                                                        (&mut pn)[0] = n10.wrapping_sub(1usize);
                                                        (&mut poffset)[0] = offset·;
                                                        let n11: usize = (&pn)[0];
                                                        cond = n11 > 0usize
                                                    };
                                                    let pos: usize = (&poffset)[0];
                                                    let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                                    let _pl_prefix: &[u8] = pl_p.0;
                                                    let pl_suffix: &[u8] = pl_p.1;
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                    { count: cur_n_v, payload: pl_suffix }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          };
                                      let len: usize =
                                          base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                              bi·
                                          );
                                      (bi·,len)
                                  },
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append { .. } =>
                                  panic!("Pulse.Lib.Dv.unreachable"),
                                _ => panic!("Incomplete pattern matching")
                            };
                        let bi·: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                            fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                res
                            );
                        let len_sz1: usize =
                            snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                res
                            );
                        let rest_sz: usize = total_sz.wrapping_sub(len_sz1);
                        let rest: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                            match ar_ml1
                            {
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                { _0: bi }
                                =>
                                  {
                                      let
                                      bi·1: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                      =
                                          match bi
                                          {
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                              =>
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                              { sr: s }
                                              =>
                                                if rest_sz == 0usize
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                }
                                                else
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                    { sr: s }
                                                },
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                              { ss: s }
                                              =>
                                                {
                                                    let s_pr: (&[cbor_raw], &[cbor_raw]) =
                                                        s.split_at(len_sz1);
                                                    let _s_prefix: &[cbor_raw] = s_pr.0;
                                                    let s_rest: &[cbor_raw] = s_pr.1;
                                                    let s_ms: (&[cbor_raw], &[cbor_raw]) =
                                                        s_rest.split_at(rest_sz);
                                                    let s_middle: &[cbor_raw] = s_ms.0;
                                                    let _s_suffix: &[cbor_raw] = s_ms.1;
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                    { ss: s_middle }
                                                },
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                              { payload: pl, .. }
                                              =>
                                                {
                                                    let mut pn: [usize; 1] = [len_sz1; 1usize];
                                                    let mut poffset: [usize; 1] = [0usize; 1usize];
                                                    let n1: usize = (&pn)[0];
                                                    let mut cond: bool = n1 > 0usize;
                                                    while
                                                    cond
                                                    {
                                                        let n10: usize = (&pn)[0];
                                                        let offset: usize = (&poffset)[0];
                                                        let offset·: usize =
                                                            jump_raw_data_item(pl, offset);
                                                        (&mut pn)[0] = n10.wrapping_sub(1usize);
                                                        (&mut poffset)[0] = offset·;
                                                        let n11: usize = (&pn)[0];
                                                        cond = n11 > 0usize
                                                    };
                                                    let pos: usize = (&poffset)[0];
                                                    let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                                    let _pl_prefix: &[u8] = pl_p.0;
                                                    let pl_suffix: &[u8] = pl_p.1;
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                    { count: rest_sz, payload: pl_suffix }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          };
                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                      { _0: bi·1 }
                                  },
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                { cb, ca, ob, before, oa, after }
                                =>
                                  {
                                      let cb·_sz: usize = append_n_before_sz(len_sz1, rest_sz, cb);
                                      let ca·_sz: usize = append_n_after_sz(len_sz1, rest_sz, cb);
                                      let ob·_sz: usize = append_off_before_sz(len_sz1, ob, cb);
                                      let oa·_sz: usize = append_off_after_sz(len_sz1, oa, ca, cb);
                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                      {
                                          cb: cb·_sz,
                                          ca: ca·_sz,
                                          ob: ob·_sz,
                                          before,
                                          oa: oa·_sz,
                                          after
                                      }
                                  },
                                _ => panic!("Incomplete pattern matching")
                            };
                        iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                        { before: bi·, after: rest }
                    };
                let total_sz0: usize =
                    mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ar_ml2);
                let it2_init: iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                    if total_sz0 == 0usize
                    {
                        iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                        {
                            before: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                            after:
                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                            { _0: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty }
                        }
                    }
                    else
                    {
                        let mut r_node: [mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw; 1] =
                            [ar_ml2; 1usize];
                        let mut r_off: [usize; 1] = [0usize; 1usize];
                        let mut r_n: [usize; 1] = [total_sz0; 1usize];
                        let mut pcontinue: [bool; 1] =
                            [! uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(ar_ml2); 1usize];
                        while
                        (&pcontinue)[0]
                        {
                            let node: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                                (&r_node)[0];
                            let cur_off_v: usize = (&r_off)[0];
                            let cur_n_v: usize = (&r_n)[0];
                            match node
                            {
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                { cb, ca, ob, before, oa, after }
                                =>
                                  {
                                      let child_n_before: usize =
                                          append_n_before_sz(cur_off_v, cur_n_v, cb);
                                      if child_n_before > 0usize
                                      {
                                          let child_off_sz: usize =
                                              append_off_before_sz(cur_off_v, ob, cb);
                                          let
                                          ib: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                          =
                                              before[0];
                                          (&mut r_node)[0] = ib;
                                          (&mut r_off)[0] = child_off_sz;
                                          (&mut r_n)[0] = child_n_before;
                                          (&mut pcontinue)[0] =
                                              !
                                              uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                  ib
                                              )
                                      }
                                      else
                                      {
                                          let child_off_sz: usize =
                                              append_off_after_sz(cur_off_v, oa, ca, cb);
                                          let child_n_sz: usize =
                                              append_n_after_sz(cur_off_v, cur_n_v, cb);
                                          let
                                          ia: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                          =
                                              after[0];
                                          (&mut r_node)[0] = ia;
                                          (&mut r_off)[0] = child_off_sz;
                                          (&mut r_n)[0] = child_n_sz;
                                          (&mut pcontinue)[0] =
                                              !
                                              uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                  ia
                                              )
                                      }
                                  },
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base { .. } =>
                                  (),
                                _ => panic!("Incomplete pattern matching")
                            }
                        };
                        let node: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw = (&r_node)[0];
                        let cur_off_v: usize = (&r_off)[0];
                        let cur_n_v: usize = (&r_n)[0];
                        let res: (base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw, usize) =
                            match node
                            {
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                { _0: bi }
                                =>
                                  {
                                      let
                                      bi·: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                      =
                                          match bi
                                          {
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                              =>
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                              { sr: s }
                                              =>
                                                if cur_n_v == 0usize
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                }
                                                else
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                    { sr: s }
                                                },
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                              { ss: s }
                                              =>
                                                {
                                                    let s_pr: (&[cbor_raw], &[cbor_raw]) =
                                                        s.split_at(cur_off_v);
                                                    let _s_prefix: &[cbor_raw] = s_pr.0;
                                                    let s_rest: &[cbor_raw] = s_pr.1;
                                                    let s_ms: (&[cbor_raw], &[cbor_raw]) =
                                                        s_rest.split_at(cur_n_v);
                                                    let s_middle: &[cbor_raw] = s_ms.0;
                                                    let _s_suffix: &[cbor_raw] = s_ms.1;
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                    { ss: s_middle }
                                                },
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                              { payload: pl, .. }
                                              =>
                                                {
                                                    let mut pn: [usize; 1] = [cur_off_v; 1usize];
                                                    let mut poffset: [usize; 1] = [0usize; 1usize];
                                                    let n1: usize = (&pn)[0];
                                                    let mut cond: bool = n1 > 0usize;
                                                    while
                                                    cond
                                                    {
                                                        let n10: usize = (&pn)[0];
                                                        let offset: usize = (&poffset)[0];
                                                        let offset·: usize =
                                                            jump_raw_data_item(pl, offset);
                                                        (&mut pn)[0] = n10.wrapping_sub(1usize);
                                                        (&mut poffset)[0] = offset·;
                                                        let n11: usize = (&pn)[0];
                                                        cond = n11 > 0usize
                                                    };
                                                    let pos: usize = (&poffset)[0];
                                                    let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                                    let _pl_prefix: &[u8] = pl_p.0;
                                                    let pl_suffix: &[u8] = pl_p.1;
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                    { count: cur_n_v, payload: pl_suffix }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          };
                                      let len: usize =
                                          base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                              bi·
                                          );
                                      (bi·,len)
                                  },
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append { .. } =>
                                  panic!("Pulse.Lib.Dv.unreachable"),
                                _ => panic!("Incomplete pattern matching")
                            };
                        let bi·: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                            fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                res
                            );
                        let len_sz1: usize =
                            snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                res
                            );
                        let rest_sz: usize = total_sz0.wrapping_sub(len_sz1);
                        let rest: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                            match ar_ml2
                            {
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                { _0: bi }
                                =>
                                  {
                                      let
                                      bi·1: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                      =
                                          match bi
                                          {
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                              =>
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                              { sr: s }
                                              =>
                                                if rest_sz == 0usize
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                }
                                                else
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                    { sr: s }
                                                },
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                              { ss: s }
                                              =>
                                                {
                                                    let s_pr: (&[cbor_raw], &[cbor_raw]) =
                                                        s.split_at(len_sz1);
                                                    let _s_prefix: &[cbor_raw] = s_pr.0;
                                                    let s_rest: &[cbor_raw] = s_pr.1;
                                                    let s_ms: (&[cbor_raw], &[cbor_raw]) =
                                                        s_rest.split_at(rest_sz);
                                                    let s_middle: &[cbor_raw] = s_ms.0;
                                                    let _s_suffix: &[cbor_raw] = s_ms.1;
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                    { ss: s_middle }
                                                },
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                              { payload: pl, .. }
                                              =>
                                                {
                                                    let mut pn: [usize; 1] = [len_sz1; 1usize];
                                                    let mut poffset: [usize; 1] = [0usize; 1usize];
                                                    let n1: usize = (&pn)[0];
                                                    let mut cond: bool = n1 > 0usize;
                                                    while
                                                    cond
                                                    {
                                                        let n10: usize = (&pn)[0];
                                                        let offset: usize = (&poffset)[0];
                                                        let offset·: usize =
                                                            jump_raw_data_item(pl, offset);
                                                        (&mut pn)[0] = n10.wrapping_sub(1usize);
                                                        (&mut poffset)[0] = offset·;
                                                        let n11: usize = (&pn)[0];
                                                        cond = n11 > 0usize
                                                    };
                                                    let pos: usize = (&poffset)[0];
                                                    let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                                    let _pl_prefix: &[u8] = pl_p.0;
                                                    let pl_suffix: &[u8] = pl_p.1;
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                    { count: rest_sz, payload: pl_suffix }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          };
                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                      { _0: bi·1 }
                                  },
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                { cb, ca, ob, before, oa, after }
                                =>
                                  {
                                      let cb·_sz: usize = append_n_before_sz(len_sz1, rest_sz, cb);
                                      let ca·_sz: usize = append_n_after_sz(len_sz1, rest_sz, cb);
                                      let ob·_sz: usize = append_off_before_sz(len_sz1, ob, cb);
                                      let oa·_sz: usize = append_off_after_sz(len_sz1, oa, ca, cb);
                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                      {
                                          cb: cb·_sz,
                                          ca: ca·_sz,
                                          ob: ob·_sz,
                                          before,
                                          oa: oa·_sz,
                                          after
                                      }
                                  },
                                _ => panic!("Incomplete pattern matching")
                            };
                        iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                        { before: bi·, after: rest }
                    };
                let mut r_it1: [iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw; 1] =
                    [it1_init; 1usize];
                let mut r_it2: [iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw; 1] =
                    [it2_init; 1usize];
                let mut r_acc: [i16; 1] = [0i16; 1usize];
                let mut r_cnt: [usize; 1] = [0usize; 1usize];
                let acc: i16 = (&r_acc)[0];
                let cnt: usize = (&r_cnt)[0];
                let mut cond: bool = cnt < len_sz && acc == 0i16;
                while
                cond
                {
                    let i: iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw = (&r_it1)[0];
                    let len_sz1: usize =
                        base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(i.before);
                    let e1: elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                        if len_sz1 == 0usize
                        { panic!("Pulse.Lib.Dv.unreachable") }
                        else
                        {
                            let x: elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                                match i.before
                                {
                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                    => panic!("Pulse.Lib.Dv.unreachable"),
                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                    { sr: s }
                                    =>
                                      {
                                          let x_val: cbor_raw = s[0];
                                          elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::EElement
                                          { _0: x_val }
                                      },
                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                    { ss: s }
                                    =>
                                      {
                                          let x_val: cbor_raw = s[0usize];
                                          elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::EElement
                                          { _0: x_val }
                                      },
                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                    { payload: pl, .. }
                                    =>
                                      {
                                          let mut pn: [usize; 1] = [0usize; 1usize];
                                          let mut poffset: [usize; 1] = [0usize; 1usize];
                                          let n1: usize = (&pn)[0];
                                          let mut cond0: bool = n1 > 0usize;
                                          while
                                          cond0
                                          {
                                              let n10: usize = (&pn)[0];
                                              let offset: usize = (&poffset)[0];
                                              let offset·: usize = jump_raw_data_item(pl, offset);
                                              (&mut pn)[0] = n10.wrapping_sub(1usize);
                                              (&mut poffset)[0] = offset·;
                                              let n11: usize = (&pn)[0];
                                              cond0 = n11 > 0usize
                                          };
                                          let pos: usize = (&poffset)[0];
                                          let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                          let _pl_prefix: &[u8] = pl_p.0;
                                          let pl_suffix: &[u8] = pl_p.1;
                                          let consumed_sz: usize =
                                              jump_raw_data_item(pl_suffix, 0usize);
                                          let pl_hd_p: (&[u8], &[u8]) =
                                              pl_suffix.split_at(consumed_sz);
                                          let pl_head: &[u8] = pl_hd_p.0;
                                          let _pl_rest: &[u8] = pl_hd_p.1;
                                          elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::ESerialized
                                          { _0: pl_head }
                                      },
                                    _ => panic!("Incomplete pattern matching")
                                };
                            if len_sz1 == 1usize
                            {
                                let total_sz1: usize =
                                    mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                        i.after
                                    );
                                let it_new: iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                                    if total_sz1 == 0usize
                                    {
                                        iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        {
                                            before:
                                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                            after:
                                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                            {
                                                _0:
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                            }
                                        }
                                    }
                                    else
                                    {
                                        let
                                        mut
                                        r_node:
                                        [mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw; 1]
                                        =
                                            [i.after; 1usize];
                                        let mut r_off: [usize; 1] = [0usize; 1usize];
                                        let mut r_n: [usize; 1] = [total_sz1; 1usize];
                                        let mut pcontinue: [bool; 1] =
                                            [!
                                                uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                    i.after
                                                );
                                                1usize];
                                        while
                                        (&pcontinue)[0]
                                        {
                                            let
                                            node: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                            =
                                                (&r_node)[0];
                                            let cur_off_v: usize = (&r_off)[0];
                                            let cur_n_v: usize = (&r_n)[0];
                                            match node
                                            {
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                { cb, ca, ob, before, oa, after }
                                                =>
                                                  {
                                                      let child_n_before: usize =
                                                          append_n_before_sz(cur_off_v, cur_n_v, cb);
                                                      if child_n_before > 0usize
                                                      {
                                                          let child_off_sz: usize =
                                                              append_off_before_sz(
                                                                  cur_off_v,
                                                                  ob,
                                                                  cb
                                                              );
                                                          let
                                                          ib:
                                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                          =
                                                              before[0];
                                                          (&mut r_node)[0] = ib;
                                                          (&mut r_off)[0] = child_off_sz;
                                                          (&mut r_n)[0] = child_n_before;
                                                          (&mut pcontinue)[0] =
                                                              !
                                                              uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                                  ib
                                                              )
                                                      }
                                                      else
                                                      {
                                                          let child_off_sz: usize =
                                                              append_off_after_sz(
                                                                  cur_off_v,
                                                                  oa,
                                                                  ca,
                                                                  cb
                                                              );
                                                          let child_n_sz: usize =
                                                              append_n_after_sz(
                                                                  cur_off_v,
                                                                  cur_n_v,
                                                                  cb
                                                              );
                                                          let
                                                          ia:
                                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                          =
                                                              after[0];
                                                          (&mut r_node)[0] = ia;
                                                          (&mut r_off)[0] = child_off_sz;
                                                          (&mut r_n)[0] = child_n_sz;
                                                          (&mut pcontinue)[0] =
                                                              !
                                                              uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                                  ia
                                                              )
                                                      }
                                                  },
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                { .. }
                                                => (),
                                                _ => panic!("Incomplete pattern matching")
                                            }
                                        };
                                        let
                                        node: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        =
                                            (&r_node)[0];
                                        let cur_off_v: usize = (&r_off)[0];
                                        let cur_n_v: usize = (&r_n)[0];
                                        let
                                        res:
                                        (base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                                        usize)
                                        =
                                            match node
                                            {
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                { _0: bi }
                                                =>
                                                  {
                                                      let
                                                      bi·:
                                                      base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                      =
                                                          match bi
                                                          {
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                              =>
                                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                              { sr: s }
                                                              =>
                                                                if cur_n_v == 0usize
                                                                {
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                                }
                                                                else
                                                                {
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                                    { sr: s }
                                                                },
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                              { ss: s }
                                                              =>
                                                                {
                                                                    let
                                                                    s_pr: (&[cbor_raw], &[cbor_raw])
                                                                    =
                                                                        s.split_at(cur_off_v);
                                                                    let _s_prefix: &[cbor_raw] =
                                                                        s_pr.0;
                                                                    let s_rest: &[cbor_raw] =
                                                                        s_pr.1;
                                                                    let
                                                                    s_ms: (&[cbor_raw], &[cbor_raw])
                                                                    =
                                                                        s_rest.split_at(cur_n_v);
                                                                    let s_middle: &[cbor_raw] =
                                                                        s_ms.0;
                                                                    let _s_suffix: &[cbor_raw] =
                                                                        s_ms.1;
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                                    { ss: s_middle }
                                                                },
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                              { payload: pl, .. }
                                                              =>
                                                                {
                                                                    let mut pn: [usize; 1] =
                                                                        [cur_off_v; 1usize];
                                                                    let mut poffset: [usize; 1] =
                                                                        [0usize; 1usize];
                                                                    let n1: usize = (&pn)[0];
                                                                    let mut cond0: bool =
                                                                        n1 > 0usize;
                                                                    while
                                                                    cond0
                                                                    {
                                                                        let n10: usize = (&pn)[0];
                                                                        let offset: usize =
                                                                            (&poffset)[0];
                                                                        let offset·: usize =
                                                                            jump_raw_data_item(
                                                                                pl,
                                                                                offset
                                                                            );
                                                                        (&mut pn)[0] =
                                                                            n10.wrapping_sub(1usize);
                                                                        (&mut poffset)[0] = offset·;
                                                                        let n11: usize = (&pn)[0];
                                                                        cond0 = n11 > 0usize
                                                                    };
                                                                    let pos: usize = (&poffset)[0];
                                                                    let pl_p: (&[u8], &[u8]) =
                                                                        pl.split_at(pos);
                                                                    let _pl_prefix: &[u8] = pl_p.0;
                                                                    let pl_suffix: &[u8] = pl_p.1;
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                                    {
                                                                        count: cur_n_v,
                                                                        payload: pl_suffix
                                                                    }
                                                                },
                                                              _ =>
                                                                panic!(
                                                                    "Incomplete pattern matching"
                                                                )
                                                          };
                                                      let len: usize =
                                                          base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                              bi·
                                                          );
                                                      (bi·,len)
                                                  },
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                { .. }
                                                => panic!("Pulse.Lib.Dv.unreachable"),
                                                _ => panic!("Incomplete pattern matching")
                                            };
                                        let
                                        bi·:
                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        =
                                            fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                                res
                                            );
                                        let len_sz2: usize =
                                            snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                                res
                                            );
                                        let rest_sz: usize = total_sz1.wrapping_sub(len_sz2);
                                        let
                                        rest: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        =
                                            match i.after
                                            {
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                { _0: bi }
                                                =>
                                                  {
                                                      let
                                                      bi·1:
                                                      base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                      =
                                                          match bi
                                                          {
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                              =>
                                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                              { sr: s }
                                                              =>
                                                                if rest_sz == 0usize
                                                                {
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                                }
                                                                else
                                                                {
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                                    { sr: s }
                                                                },
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                              { ss: s }
                                                              =>
                                                                {
                                                                    let
                                                                    s_pr: (&[cbor_raw], &[cbor_raw])
                                                                    =
                                                                        s.split_at(len_sz2);
                                                                    let _s_prefix: &[cbor_raw] =
                                                                        s_pr.0;
                                                                    let s_rest: &[cbor_raw] =
                                                                        s_pr.1;
                                                                    let
                                                                    s_ms: (&[cbor_raw], &[cbor_raw])
                                                                    =
                                                                        s_rest.split_at(rest_sz);
                                                                    let s_middle: &[cbor_raw] =
                                                                        s_ms.0;
                                                                    let _s_suffix: &[cbor_raw] =
                                                                        s_ms.1;
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                                    { ss: s_middle }
                                                                },
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                              { payload: pl, .. }
                                                              =>
                                                                {
                                                                    let mut pn: [usize; 1] =
                                                                        [len_sz2; 1usize];
                                                                    let mut poffset: [usize; 1] =
                                                                        [0usize; 1usize];
                                                                    let n1: usize = (&pn)[0];
                                                                    let mut cond0: bool =
                                                                        n1 > 0usize;
                                                                    while
                                                                    cond0
                                                                    {
                                                                        let n10: usize = (&pn)[0];
                                                                        let offset: usize =
                                                                            (&poffset)[0];
                                                                        let offset·: usize =
                                                                            jump_raw_data_item(
                                                                                pl,
                                                                                offset
                                                                            );
                                                                        (&mut pn)[0] =
                                                                            n10.wrapping_sub(1usize);
                                                                        (&mut poffset)[0] = offset·;
                                                                        let n11: usize = (&pn)[0];
                                                                        cond0 = n11 > 0usize
                                                                    };
                                                                    let pos: usize = (&poffset)[0];
                                                                    let pl_p: (&[u8], &[u8]) =
                                                                        pl.split_at(pos);
                                                                    let _pl_prefix: &[u8] = pl_p.0;
                                                                    let pl_suffix: &[u8] = pl_p.1;
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                                    {
                                                                        count: rest_sz,
                                                                        payload: pl_suffix
                                                                    }
                                                                },
                                                              _ =>
                                                                panic!(
                                                                    "Incomplete pattern matching"
                                                                )
                                                          };
                                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                      { _0: bi·1 }
                                                  },
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                { cb, ca, ob, before, oa, after }
                                                =>
                                                  {
                                                      let cb·_sz: usize =
                                                          append_n_before_sz(len_sz2, rest_sz, cb);
                                                      let ca·_sz: usize =
                                                          append_n_after_sz(len_sz2, rest_sz, cb);
                                                      let ob·_sz: usize =
                                                          append_off_before_sz(len_sz2, ob, cb);
                                                      let oa·_sz: usize =
                                                          append_off_after_sz(len_sz2, oa, ca, cb);
                                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                      {
                                                          cb: cb·_sz,
                                                          ca: ca·_sz,
                                                          ob: ob·_sz,
                                                          before,
                                                          oa: oa·_sz,
                                                          after
                                                      }
                                                  },
                                                _ => panic!("Incomplete pattern matching")
                                            };
                                        iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        { before: bi·, after: rest }
                                    };
                                (&mut r_it1)[0] = it_new;
                                x
                            }
                            else
                            {
                                let n_tail_sz: usize = len_sz1.wrapping_sub(1usize);
                                let
                                bi_tail: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                =
                                    match i.before
                                    {
                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                        =>
                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                        { sr: s }
                                        =>
                                          if n_tail_sz == 0usize
                                          {
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                          }
                                          else
                                          {
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                              { sr: s }
                                          },
                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                        { ss: s }
                                        =>
                                          {
                                              let s_pr: (&[cbor_raw], &[cbor_raw]) =
                                                  s.split_at(1usize);
                                              let _s_prefix: &[cbor_raw] = s_pr.0;
                                              let s_rest: &[cbor_raw] = s_pr.1;
                                              let s_ms: (&[cbor_raw], &[cbor_raw]) =
                                                  s_rest.split_at(n_tail_sz);
                                              let s_middle: &[cbor_raw] = s_ms.0;
                                              let _s_suffix: &[cbor_raw] = s_ms.1;
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                              { ss: s_middle }
                                          },
                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                        { payload: pl, .. }
                                        =>
                                          {
                                              let mut pn: [usize; 1] = [1usize; 1usize];
                                              let mut poffset: [usize; 1] = [0usize; 1usize];
                                              let n1: usize = (&pn)[0];
                                              let mut cond0: bool = n1 > 0usize;
                                              while
                                              cond0
                                              {
                                                  let n10: usize = (&pn)[0];
                                                  let offset: usize = (&poffset)[0];
                                                  let offset·: usize =
                                                      jump_raw_data_item(pl, offset);
                                                  (&mut pn)[0] = n10.wrapping_sub(1usize);
                                                  (&mut poffset)[0] = offset·;
                                                  let n11: usize = (&pn)[0];
                                                  cond0 = n11 > 0usize
                                              };
                                              let pos: usize = (&poffset)[0];
                                              let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                              let _pl_prefix: &[u8] = pl_p.0;
                                              let pl_suffix: &[u8] = pl_p.1;
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                              { count: n_tail_sz, payload: pl_suffix }
                                          },
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                let it_new: iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                                    iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                    { before: bi_tail, after: i.after };
                                (&mut r_it1)[0] = it_new;
                                x
                            }
                        };
                    let i0: iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw = (&r_it2)[0];
                    let len_sz10: usize =
                        base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(i0.before);
                    let e2: elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                        if len_sz10 == 0usize
                        { panic!("Pulse.Lib.Dv.unreachable") }
                        else
                        {
                            let x: elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                                match i0.before
                                {
                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                    => panic!("Pulse.Lib.Dv.unreachable"),
                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                    { sr: s }
                                    =>
                                      {
                                          let x_val: cbor_raw = s[0];
                                          elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::EElement
                                          { _0: x_val }
                                      },
                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                    { ss: s }
                                    =>
                                      {
                                          let x_val: cbor_raw = s[0usize];
                                          elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::EElement
                                          { _0: x_val }
                                      },
                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                    { payload: pl, .. }
                                    =>
                                      {
                                          let mut pn: [usize; 1] = [0usize; 1usize];
                                          let mut poffset: [usize; 1] = [0usize; 1usize];
                                          let n1: usize = (&pn)[0];
                                          let mut cond0: bool = n1 > 0usize;
                                          while
                                          cond0
                                          {
                                              let n10: usize = (&pn)[0];
                                              let offset: usize = (&poffset)[0];
                                              let offset·: usize = jump_raw_data_item(pl, offset);
                                              (&mut pn)[0] = n10.wrapping_sub(1usize);
                                              (&mut poffset)[0] = offset·;
                                              let n11: usize = (&pn)[0];
                                              cond0 = n11 > 0usize
                                          };
                                          let pos: usize = (&poffset)[0];
                                          let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                          let _pl_prefix: &[u8] = pl_p.0;
                                          let pl_suffix: &[u8] = pl_p.1;
                                          let consumed_sz: usize =
                                              jump_raw_data_item(pl_suffix, 0usize);
                                          let pl_hd_p: (&[u8], &[u8]) =
                                              pl_suffix.split_at(consumed_sz);
                                          let pl_head: &[u8] = pl_hd_p.0;
                                          let _pl_rest: &[u8] = pl_hd_p.1;
                                          elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::ESerialized
                                          { _0: pl_head }
                                      },
                                    _ => panic!("Incomplete pattern matching")
                                };
                            if len_sz10 == 1usize
                            {
                                let total_sz1: usize =
                                    mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                        i0.after
                                    );
                                let it_new: iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                                    if total_sz1 == 0usize
                                    {
                                        iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        {
                                            before:
                                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                            after:
                                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                            {
                                                _0:
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                            }
                                        }
                                    }
                                    else
                                    {
                                        let
                                        mut
                                        r_node:
                                        [mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw; 1]
                                        =
                                            [i0.after; 1usize];
                                        let mut r_off: [usize; 1] = [0usize; 1usize];
                                        let mut r_n: [usize; 1] = [total_sz1; 1usize];
                                        let mut pcontinue: [bool; 1] =
                                            [!
                                                uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                    i0.after
                                                );
                                                1usize];
                                        while
                                        (&pcontinue)[0]
                                        {
                                            let
                                            node: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                            =
                                                (&r_node)[0];
                                            let cur_off_v: usize = (&r_off)[0];
                                            let cur_n_v: usize = (&r_n)[0];
                                            match node
                                            {
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                { cb, ca, ob, before, oa, after }
                                                =>
                                                  {
                                                      let child_n_before: usize =
                                                          append_n_before_sz(cur_off_v, cur_n_v, cb);
                                                      if child_n_before > 0usize
                                                      {
                                                          let child_off_sz: usize =
                                                              append_off_before_sz(
                                                                  cur_off_v,
                                                                  ob,
                                                                  cb
                                                              );
                                                          let
                                                          ib:
                                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                          =
                                                              before[0];
                                                          (&mut r_node)[0] = ib;
                                                          (&mut r_off)[0] = child_off_sz;
                                                          (&mut r_n)[0] = child_n_before;
                                                          (&mut pcontinue)[0] =
                                                              !
                                                              uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                                  ib
                                                              )
                                                      }
                                                      else
                                                      {
                                                          let child_off_sz: usize =
                                                              append_off_after_sz(
                                                                  cur_off_v,
                                                                  oa,
                                                                  ca,
                                                                  cb
                                                              );
                                                          let child_n_sz: usize =
                                                              append_n_after_sz(
                                                                  cur_off_v,
                                                                  cur_n_v,
                                                                  cb
                                                              );
                                                          let
                                                          ia:
                                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                          =
                                                              after[0];
                                                          (&mut r_node)[0] = ia;
                                                          (&mut r_off)[0] = child_off_sz;
                                                          (&mut r_n)[0] = child_n_sz;
                                                          (&mut pcontinue)[0] =
                                                              !
                                                              uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                                  ia
                                                              )
                                                      }
                                                  },
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                { .. }
                                                => (),
                                                _ => panic!("Incomplete pattern matching")
                                            }
                                        };
                                        let
                                        node: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        =
                                            (&r_node)[0];
                                        let cur_off_v: usize = (&r_off)[0];
                                        let cur_n_v: usize = (&r_n)[0];
                                        let
                                        res:
                                        (base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                                        usize)
                                        =
                                            match node
                                            {
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                { _0: bi }
                                                =>
                                                  {
                                                      let
                                                      bi·:
                                                      base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                      =
                                                          match bi
                                                          {
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                              =>
                                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                              { sr: s }
                                                              =>
                                                                if cur_n_v == 0usize
                                                                {
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                                }
                                                                else
                                                                {
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                                    { sr: s }
                                                                },
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                              { ss: s }
                                                              =>
                                                                {
                                                                    let
                                                                    s_pr: (&[cbor_raw], &[cbor_raw])
                                                                    =
                                                                        s.split_at(cur_off_v);
                                                                    let _s_prefix: &[cbor_raw] =
                                                                        s_pr.0;
                                                                    let s_rest: &[cbor_raw] =
                                                                        s_pr.1;
                                                                    let
                                                                    s_ms: (&[cbor_raw], &[cbor_raw])
                                                                    =
                                                                        s_rest.split_at(cur_n_v);
                                                                    let s_middle: &[cbor_raw] =
                                                                        s_ms.0;
                                                                    let _s_suffix: &[cbor_raw] =
                                                                        s_ms.1;
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                                    { ss: s_middle }
                                                                },
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                              { payload: pl, .. }
                                                              =>
                                                                {
                                                                    let mut pn: [usize; 1] =
                                                                        [cur_off_v; 1usize];
                                                                    let mut poffset: [usize; 1] =
                                                                        [0usize; 1usize];
                                                                    let n1: usize = (&pn)[0];
                                                                    let mut cond0: bool =
                                                                        n1 > 0usize;
                                                                    while
                                                                    cond0
                                                                    {
                                                                        let n10: usize = (&pn)[0];
                                                                        let offset: usize =
                                                                            (&poffset)[0];
                                                                        let offset·: usize =
                                                                            jump_raw_data_item(
                                                                                pl,
                                                                                offset
                                                                            );
                                                                        (&mut pn)[0] =
                                                                            n10.wrapping_sub(1usize);
                                                                        (&mut poffset)[0] = offset·;
                                                                        let n11: usize = (&pn)[0];
                                                                        cond0 = n11 > 0usize
                                                                    };
                                                                    let pos: usize = (&poffset)[0];
                                                                    let pl_p: (&[u8], &[u8]) =
                                                                        pl.split_at(pos);
                                                                    let _pl_prefix: &[u8] = pl_p.0;
                                                                    let pl_suffix: &[u8] = pl_p.1;
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                                    {
                                                                        count: cur_n_v,
                                                                        payload: pl_suffix
                                                                    }
                                                                },
                                                              _ =>
                                                                panic!(
                                                                    "Incomplete pattern matching"
                                                                )
                                                          };
                                                      let len: usize =
                                                          base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                              bi·
                                                          );
                                                      (bi·,len)
                                                  },
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                { .. }
                                                => panic!("Pulse.Lib.Dv.unreachable"),
                                                _ => panic!("Incomplete pattern matching")
                                            };
                                        let
                                        bi·:
                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        =
                                            fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                                res
                                            );
                                        let len_sz2: usize =
                                            snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                                res
                                            );
                                        let rest_sz: usize = total_sz1.wrapping_sub(len_sz2);
                                        let
                                        rest: mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        =
                                            match i0.after
                                            {
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                { _0: bi }
                                                =>
                                                  {
                                                      let
                                                      bi·1:
                                                      base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                      =
                                                          match bi
                                                          {
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                              =>
                                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                              { sr: s }
                                                              =>
                                                                if rest_sz == 0usize
                                                                {
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                                }
                                                                else
                                                                {
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                                    { sr: s }
                                                                },
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                              { ss: s }
                                                              =>
                                                                {
                                                                    let
                                                                    s_pr: (&[cbor_raw], &[cbor_raw])
                                                                    =
                                                                        s.split_at(len_sz2);
                                                                    let _s_prefix: &[cbor_raw] =
                                                                        s_pr.0;
                                                                    let s_rest: &[cbor_raw] =
                                                                        s_pr.1;
                                                                    let
                                                                    s_ms: (&[cbor_raw], &[cbor_raw])
                                                                    =
                                                                        s_rest.split_at(rest_sz);
                                                                    let s_middle: &[cbor_raw] =
                                                                        s_ms.0;
                                                                    let _s_suffix: &[cbor_raw] =
                                                                        s_ms.1;
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                                    { ss: s_middle }
                                                                },
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                              { payload: pl, .. }
                                                              =>
                                                                {
                                                                    let mut pn: [usize; 1] =
                                                                        [len_sz2; 1usize];
                                                                    let mut poffset: [usize; 1] =
                                                                        [0usize; 1usize];
                                                                    let n1: usize = (&pn)[0];
                                                                    let mut cond0: bool =
                                                                        n1 > 0usize;
                                                                    while
                                                                    cond0
                                                                    {
                                                                        let n10: usize = (&pn)[0];
                                                                        let offset: usize =
                                                                            (&poffset)[0];
                                                                        let offset·: usize =
                                                                            jump_raw_data_item(
                                                                                pl,
                                                                                offset
                                                                            );
                                                                        (&mut pn)[0] =
                                                                            n10.wrapping_sub(1usize);
                                                                        (&mut poffset)[0] = offset·;
                                                                        let n11: usize = (&pn)[0];
                                                                        cond0 = n11 > 0usize
                                                                    };
                                                                    let pos: usize = (&poffset)[0];
                                                                    let pl_p: (&[u8], &[u8]) =
                                                                        pl.split_at(pos);
                                                                    let _pl_prefix: &[u8] = pl_p.0;
                                                                    let pl_suffix: &[u8] = pl_p.1;
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                                    {
                                                                        count: rest_sz,
                                                                        payload: pl_suffix
                                                                    }
                                                                },
                                                              _ =>
                                                                panic!(
                                                                    "Incomplete pattern matching"
                                                                )
                                                          };
                                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                      { _0: bi·1 }
                                                  },
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                { cb, ca, ob, before, oa, after }
                                                =>
                                                  {
                                                      let cb·_sz: usize =
                                                          append_n_before_sz(len_sz2, rest_sz, cb);
                                                      let ca·_sz: usize =
                                                          append_n_after_sz(len_sz2, rest_sz, cb);
                                                      let ob·_sz: usize =
                                                          append_off_before_sz(len_sz2, ob, cb);
                                                      let oa·_sz: usize =
                                                          append_off_after_sz(len_sz2, oa, ca, cb);
                                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                      {
                                                          cb: cb·_sz,
                                                          ca: ca·_sz,
                                                          ob: ob·_sz,
                                                          before,
                                                          oa: oa·_sz,
                                                          after
                                                      }
                                                  },
                                                _ => panic!("Incomplete pattern matching")
                                            };
                                        iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        { before: bi·, after: rest }
                                    };
                                (&mut r_it2)[0] = it_new;
                                x
                            }
                            else
                            {
                                let n_tail_sz: usize = len_sz10.wrapping_sub(1usize);
                                let
                                bi_tail: base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                =
                                    match i0.before
                                    {
                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                        =>
                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                        { sr: s }
                                        =>
                                          if n_tail_sz == 0usize
                                          {
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                          }
                                          else
                                          {
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                              { sr: s }
                                          },
                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                        { ss: s }
                                        =>
                                          {
                                              let s_pr: (&[cbor_raw], &[cbor_raw]) =
                                                  s.split_at(1usize);
                                              let _s_prefix: &[cbor_raw] = s_pr.0;
                                              let s_rest: &[cbor_raw] = s_pr.1;
                                              let s_ms: (&[cbor_raw], &[cbor_raw]) =
                                                  s_rest.split_at(n_tail_sz);
                                              let s_middle: &[cbor_raw] = s_ms.0;
                                              let _s_suffix: &[cbor_raw] = s_ms.1;
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                              { ss: s_middle }
                                          },
                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                        { payload: pl, .. }
                                        =>
                                          {
                                              let mut pn: [usize; 1] = [1usize; 1usize];
                                              let mut poffset: [usize; 1] = [0usize; 1usize];
                                              let n1: usize = (&pn)[0];
                                              let mut cond0: bool = n1 > 0usize;
                                              while
                                              cond0
                                              {
                                                  let n10: usize = (&pn)[0];
                                                  let offset: usize = (&poffset)[0];
                                                  let offset·: usize =
                                                      jump_raw_data_item(pl, offset);
                                                  (&mut pn)[0] = n10.wrapping_sub(1usize);
                                                  (&mut poffset)[0] = offset·;
                                                  let n11: usize = (&pn)[0];
                                                  cond0 = n11 > 0usize
                                              };
                                              let pos: usize = (&poffset)[0];
                                              let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                              let _pl_prefix: &[u8] = pl_p.0;
                                              let pl_suffix: &[u8] = pl_p.1;
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                              { count: n_tail_sz, payload: pl_suffix }
                                          },
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                let it_new: iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                                    iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                    { before: bi_tail, after: i0.after };
                                (&mut r_it2)[0] = it_new;
                                x
                            }
                        };
                    let old_cnt: usize = (&r_cnt)[0];
                    match e1
                    {
                        elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::EElement
                        { _0: xx1 }
                        =>
                          match e2
                          {
                              elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::EElement
                              { _0: xx2 }
                              =>
                                {
                                    let r2: i16 = impl_cbor_compare_fuel(xx1, xx2);
                                    (&mut r_acc)[0] = r2;
                                    (&mut r_cnt)[0] = old_cnt.wrapping_add(1usize)
                                },
                              elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::ESerialized
                              { _0: s2 }
                              =>
                                {
                                    let xx2: cbor_raw = cbor_raw_read_fuel(s2);
                                    let r2: i16 = impl_cbor_compare_fuel(xx1, xx2);
                                    (&mut r_acc)[0] = r2;
                                    (&mut r_cnt)[0] = old_cnt.wrapping_add(1usize)
                                },
                              _ => panic!("Incomplete pattern matching")
                          },
                        elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::ESerialized
                        { _0: s1 }
                        =>
                          match e2
                          {
                              elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::EElement
                              { _0: xx2 }
                              =>
                                {
                                    let xx1: cbor_raw = cbor_raw_read_fuel(s1);
                                    let r2: i16 = impl_cbor_compare_fuel(xx1, xx2);
                                    (&mut r_acc)[0] = r2;
                                    (&mut r_cnt)[0] = old_cnt.wrapping_add(1usize)
                                },
                              elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::ESerialized
                              { _0: s2 }
                              =>
                                {
                                    let r2: i16 = byte_compare_pts_to_parsed_data_item(s1, s2);
                                    (&mut r_acc)[0] = r2;
                                    (&mut r_cnt)[0] = old_cnt.wrapping_add(1usize)
                                },
                              _ => panic!("Incomplete pattern matching")
                          },
                        _ => panic!("Incomplete pattern matching")
                    };
                    let acc0: i16 = (&r_acc)[0];
                    let cnt0: usize = (&r_cnt)[0];
                    cond = cnt0 < len_sz && acc0 == 0i16
                };
                (&r_acc)[0]
            }
            else
            { cl }
        }
        else if ty1 == cbor_major_type_map
        {
            let len1: raw_uint64 = cbor_raw_map_raw_uint64(x1);
            let len2: raw_uint64 = cbor_raw_map_raw_uint64(x2);
            let cl: i16 = impl_raw_uint64_compare(len1, len2);
            if cl == 0i16
            {
                let len_sz: usize = len1.value as usize;
                let
                map_ml1:
                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                =
                    cbor_raw_get_map_aux(x1);
                let
                map_ml2:
                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                =
                    cbor_raw_get_map_aux(x2);
                let total_sz: usize =
                    mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                        map_ml1
                    );
                let
                it1_init:
                iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                =
                    if total_sz == 0usize
                    {
                        iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                        {
                            before:
                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                            after:
                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                            {
                                _0:
                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                            }
                        }
                    }
                    else
                    {
                        let
                        mut
                        r_node:
                        [mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;
                        1]
                        =
                            [map_ml1; 1usize];
                        let mut r_off: [usize; 1] = [0usize; 1usize];
                        let mut r_n: [usize; 1] = [total_sz; 1usize];
                        let mut pcontinue: [bool; 1] =
                            [!
                                uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                    map_ml1
                                );
                                1usize];
                        while
                        (&pcontinue)[0]
                        {
                            let
                            node:
                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                            =
                                (&r_node)[0];
                            let cur_off_v: usize = (&r_off)[0];
                            let cur_n_v: usize = (&r_n)[0];
                            match node
                            {
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                { cb, ca, ob, before, oa, after }
                                =>
                                  {
                                      let child_n_before: usize =
                                          append_n_before_sz(cur_off_v, cur_n_v, cb);
                                      if child_n_before > 0usize
                                      {
                                          let child_off_sz: usize =
                                              append_off_before_sz(cur_off_v, ob, cb);
                                          let
                                          ib:
                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                          =
                                              before[0];
                                          (&mut r_node)[0] = ib;
                                          (&mut r_off)[0] = child_off_sz;
                                          (&mut r_n)[0] = child_n_before;
                                          (&mut pcontinue)[0] =
                                              !
                                              uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                  ib
                                              )
                                      }
                                      else
                                      {
                                          let child_off_sz: usize =
                                              append_off_after_sz(cur_off_v, oa, ca, cb);
                                          let child_n_sz: usize =
                                              append_n_after_sz(cur_off_v, cur_n_v, cb);
                                          let
                                          ia:
                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                          =
                                              after[0];
                                          (&mut r_node)[0] = ia;
                                          (&mut r_off)[0] = child_off_sz;
                                          (&mut r_n)[0] = child_n_sz;
                                          (&mut pcontinue)[0] =
                                              !
                                              uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                  ia
                                              )
                                      }
                                  },
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                { .. }
                                => (),
                                _ => panic!("Incomplete pattern matching")
                            }
                        };
                        let
                        node:
                        mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                        =
                            (&r_node)[0];
                        let cur_off_v: usize = (&r_off)[0];
                        let cur_n_v: usize = (&r_n)[0];
                        let
                        res:
                        (base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                        usize)
                        =
                            match node
                            {
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                { _0: bi }
                                =>
                                  {
                                      let
                                      bi·:
                                      base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                      =
                                          match bi
                                          {
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                              =>
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                              { sr: s }
                                              =>
                                                if cur_n_v == 0usize
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                }
                                                else
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                    { sr: s }
                                                },
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                              { ss: s }
                                              =>
                                                {
                                                    let
                                                    s_pr:
                                                    (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                    =
                                                        s.split_at(cur_off_v);
                                                    let
                                                    _s_prefix:
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                    =
                                                        s_pr.0;
                                                    let
                                                    s_rest:
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                    =
                                                        s_pr.1;
                                                    let
                                                    s_ms:
                                                    (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                    =
                                                        s_rest.split_at(cur_n_v);
                                                    let
                                                    s_middle:
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                    =
                                                        s_ms.0;
                                                    let
                                                    _s_suffix:
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                    =
                                                        s_ms.1;
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                    { ss: s_middle }
                                                },
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                              { payload: pl, .. }
                                              =>
                                                {
                                                    let mut pn: [usize; 1] = [cur_off_v; 1usize];
                                                    let mut poffset: [usize; 1] = [0usize; 1usize];
                                                    let n1: usize = (&pn)[0];
                                                    let mut cond: bool = n1 > 0usize;
                                                    while
                                                    cond
                                                    {
                                                        let n10: usize = (&pn)[0];
                                                        let offset: usize = (&poffset)[0];
                                                        let off1: usize =
                                                            jump_raw_data_item(pl, offset);
                                                        let offset·: usize =
                                                            jump_raw_data_item(pl, off1);
                                                        (&mut pn)[0] = n10.wrapping_sub(1usize);
                                                        (&mut poffset)[0] = offset·;
                                                        let n11: usize = (&pn)[0];
                                                        cond = n11 > 0usize
                                                    };
                                                    let pos: usize = (&poffset)[0];
                                                    let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                                    let _pl_prefix: &[u8] = pl_p.0;
                                                    let pl_suffix: &[u8] = pl_p.1;
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                    { count: cur_n_v, payload: pl_suffix }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          };
                                      let len: usize =
                                          base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                              bi·
                                          );
                                      (bi·,len)
                                  },
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                { .. }
                                => panic!("Pulse.Lib.Dv.unreachable"),
                                _ => panic!("Incomplete pattern matching")
                            };
                        let
                        bi·:
                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                        =
                            fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                res
                            );
                        let len_sz1: usize =
                            snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                res
                            );
                        let rest_sz: usize = total_sz.wrapping_sub(len_sz1);
                        let
                        rest:
                        mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                        =
                            match map_ml1
                            {
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                { _0: bi }
                                =>
                                  {
                                      let
                                      bi·1:
                                      base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                      =
                                          match bi
                                          {
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                              =>
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                              { sr: s }
                                              =>
                                                if rest_sz == 0usize
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                }
                                                else
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                    { sr: s }
                                                },
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                              { ss: s }
                                              =>
                                                {
                                                    let
                                                    s_pr:
                                                    (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                    =
                                                        s.split_at(len_sz1);
                                                    let
                                                    _s_prefix:
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                    =
                                                        s_pr.0;
                                                    let
                                                    s_rest:
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                    =
                                                        s_pr.1;
                                                    let
                                                    s_ms:
                                                    (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                    =
                                                        s_rest.split_at(rest_sz);
                                                    let
                                                    s_middle:
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                    =
                                                        s_ms.0;
                                                    let
                                                    _s_suffix:
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                    =
                                                        s_ms.1;
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                    { ss: s_middle }
                                                },
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                              { payload: pl, .. }
                                              =>
                                                {
                                                    let mut pn: [usize; 1] = [len_sz1; 1usize];
                                                    let mut poffset: [usize; 1] = [0usize; 1usize];
                                                    let n1: usize = (&pn)[0];
                                                    let mut cond: bool = n1 > 0usize;
                                                    while
                                                    cond
                                                    {
                                                        let n10: usize = (&pn)[0];
                                                        let offset: usize = (&poffset)[0];
                                                        let off1: usize =
                                                            jump_raw_data_item(pl, offset);
                                                        let offset·: usize =
                                                            jump_raw_data_item(pl, off1);
                                                        (&mut pn)[0] = n10.wrapping_sub(1usize);
                                                        (&mut poffset)[0] = offset·;
                                                        let n11: usize = (&pn)[0];
                                                        cond = n11 > 0usize
                                                    };
                                                    let pos: usize = (&poffset)[0];
                                                    let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                                    let _pl_prefix: &[u8] = pl_p.0;
                                                    let pl_suffix: &[u8] = pl_p.1;
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                    { count: rest_sz, payload: pl_suffix }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          };
                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                      { _0: bi·1 }
                                  },
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                { cb, ca, ob, before, oa, after }
                                =>
                                  {
                                      let cb·_sz: usize = append_n_before_sz(len_sz1, rest_sz, cb);
                                      let ca·_sz: usize = append_n_after_sz(len_sz1, rest_sz, cb);
                                      let ob·_sz: usize = append_off_before_sz(len_sz1, ob, cb);
                                      let oa·_sz: usize = append_off_after_sz(len_sz1, oa, ca, cb);
                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                      {
                                          cb: cb·_sz,
                                          ca: ca·_sz,
                                          ob: ob·_sz,
                                          before,
                                          oa: oa·_sz,
                                          after
                                      }
                                  },
                                _ => panic!("Incomplete pattern matching")
                            };
                        iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                        { before: bi·, after: rest }
                    };
                let total_sz0: usize =
                    mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                        map_ml2
                    );
                let
                it2_init:
                iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                =
                    if total_sz0 == 0usize
                    {
                        iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                        {
                            before:
                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                            after:
                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                            {
                                _0:
                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                            }
                        }
                    }
                    else
                    {
                        let
                        mut
                        r_node:
                        [mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;
                        1]
                        =
                            [map_ml2; 1usize];
                        let mut r_off: [usize; 1] = [0usize; 1usize];
                        let mut r_n: [usize; 1] = [total_sz0; 1usize];
                        let mut pcontinue: [bool; 1] =
                            [!
                                uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                    map_ml2
                                );
                                1usize];
                        while
                        (&pcontinue)[0]
                        {
                            let
                            node:
                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                            =
                                (&r_node)[0];
                            let cur_off_v: usize = (&r_off)[0];
                            let cur_n_v: usize = (&r_n)[0];
                            match node
                            {
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                { cb, ca, ob, before, oa, after }
                                =>
                                  {
                                      let child_n_before: usize =
                                          append_n_before_sz(cur_off_v, cur_n_v, cb);
                                      if child_n_before > 0usize
                                      {
                                          let child_off_sz: usize =
                                              append_off_before_sz(cur_off_v, ob, cb);
                                          let
                                          ib:
                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                          =
                                              before[0];
                                          (&mut r_node)[0] = ib;
                                          (&mut r_off)[0] = child_off_sz;
                                          (&mut r_n)[0] = child_n_before;
                                          (&mut pcontinue)[0] =
                                              !
                                              uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                  ib
                                              )
                                      }
                                      else
                                      {
                                          let child_off_sz: usize =
                                              append_off_after_sz(cur_off_v, oa, ca, cb);
                                          let child_n_sz: usize =
                                              append_n_after_sz(cur_off_v, cur_n_v, cb);
                                          let
                                          ia:
                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                          =
                                              after[0];
                                          (&mut r_node)[0] = ia;
                                          (&mut r_off)[0] = child_off_sz;
                                          (&mut r_n)[0] = child_n_sz;
                                          (&mut pcontinue)[0] =
                                              !
                                              uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                  ia
                                              )
                                      }
                                  },
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                { .. }
                                => (),
                                _ => panic!("Incomplete pattern matching")
                            }
                        };
                        let
                        node:
                        mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                        =
                            (&r_node)[0];
                        let cur_off_v: usize = (&r_off)[0];
                        let cur_n_v: usize = (&r_n)[0];
                        let
                        res:
                        (base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                        usize)
                        =
                            match node
                            {
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                { _0: bi }
                                =>
                                  {
                                      let
                                      bi·:
                                      base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                      =
                                          match bi
                                          {
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                              =>
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                              { sr: s }
                                              =>
                                                if cur_n_v == 0usize
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                }
                                                else
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                    { sr: s }
                                                },
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                              { ss: s }
                                              =>
                                                {
                                                    let
                                                    s_pr:
                                                    (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                    =
                                                        s.split_at(cur_off_v);
                                                    let
                                                    _s_prefix:
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                    =
                                                        s_pr.0;
                                                    let
                                                    s_rest:
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                    =
                                                        s_pr.1;
                                                    let
                                                    s_ms:
                                                    (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                    =
                                                        s_rest.split_at(cur_n_v);
                                                    let
                                                    s_middle:
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                    =
                                                        s_ms.0;
                                                    let
                                                    _s_suffix:
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                    =
                                                        s_ms.1;
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                    { ss: s_middle }
                                                },
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                              { payload: pl, .. }
                                              =>
                                                {
                                                    let mut pn: [usize; 1] = [cur_off_v; 1usize];
                                                    let mut poffset: [usize; 1] = [0usize; 1usize];
                                                    let n1: usize = (&pn)[0];
                                                    let mut cond: bool = n1 > 0usize;
                                                    while
                                                    cond
                                                    {
                                                        let n10: usize = (&pn)[0];
                                                        let offset: usize = (&poffset)[0];
                                                        let off1: usize =
                                                            jump_raw_data_item(pl, offset);
                                                        let offset·: usize =
                                                            jump_raw_data_item(pl, off1);
                                                        (&mut pn)[0] = n10.wrapping_sub(1usize);
                                                        (&mut poffset)[0] = offset·;
                                                        let n11: usize = (&pn)[0];
                                                        cond = n11 > 0usize
                                                    };
                                                    let pos: usize = (&poffset)[0];
                                                    let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                                    let _pl_prefix: &[u8] = pl_p.0;
                                                    let pl_suffix: &[u8] = pl_p.1;
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                    { count: cur_n_v, payload: pl_suffix }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          };
                                      let len: usize =
                                          base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                              bi·
                                          );
                                      (bi·,len)
                                  },
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                { .. }
                                => panic!("Pulse.Lib.Dv.unreachable"),
                                _ => panic!("Incomplete pattern matching")
                            };
                        let
                        bi·:
                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                        =
                            fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                res
                            );
                        let len_sz1: usize =
                            snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                res
                            );
                        let rest_sz: usize = total_sz0.wrapping_sub(len_sz1);
                        let
                        rest:
                        mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                        =
                            match map_ml2
                            {
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                { _0: bi }
                                =>
                                  {
                                      let
                                      bi·1:
                                      base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                      =
                                          match bi
                                          {
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                              =>
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                              { sr: s }
                                              =>
                                                if rest_sz == 0usize
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                }
                                                else
                                                {
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                    { sr: s }
                                                },
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                              { ss: s }
                                              =>
                                                {
                                                    let
                                                    s_pr:
                                                    (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                    =
                                                        s.split_at(len_sz1);
                                                    let
                                                    _s_prefix:
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                    =
                                                        s_pr.0;
                                                    let
                                                    s_rest:
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                    =
                                                        s_pr.1;
                                                    let
                                                    s_ms:
                                                    (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                    =
                                                        s_rest.split_at(rest_sz);
                                                    let
                                                    s_middle:
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                    =
                                                        s_ms.0;
                                                    let
                                                    _s_suffix:
                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                    =
                                                        s_ms.1;
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                    { ss: s_middle }
                                                },
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                              { payload: pl, .. }
                                              =>
                                                {
                                                    let mut pn: [usize; 1] = [len_sz1; 1usize];
                                                    let mut poffset: [usize; 1] = [0usize; 1usize];
                                                    let n1: usize = (&pn)[0];
                                                    let mut cond: bool = n1 > 0usize;
                                                    while
                                                    cond
                                                    {
                                                        let n10: usize = (&pn)[0];
                                                        let offset: usize = (&poffset)[0];
                                                        let off1: usize =
                                                            jump_raw_data_item(pl, offset);
                                                        let offset·: usize =
                                                            jump_raw_data_item(pl, off1);
                                                        (&mut pn)[0] = n10.wrapping_sub(1usize);
                                                        (&mut poffset)[0] = offset·;
                                                        let n11: usize = (&pn)[0];
                                                        cond = n11 > 0usize
                                                    };
                                                    let pos: usize = (&poffset)[0];
                                                    let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                                    let _pl_prefix: &[u8] = pl_p.0;
                                                    let pl_suffix: &[u8] = pl_p.1;
                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                    { count: rest_sz, payload: pl_suffix }
                                                },
                                              _ => panic!("Incomplete pattern matching")
                                          };
                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                      { _0: bi·1 }
                                  },
                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                { cb, ca, ob, before, oa, after }
                                =>
                                  {
                                      let cb·_sz: usize = append_n_before_sz(len_sz1, rest_sz, cb);
                                      let ca·_sz: usize = append_n_after_sz(len_sz1, rest_sz, cb);
                                      let ob·_sz: usize = append_off_before_sz(len_sz1, ob, cb);
                                      let oa·_sz: usize = append_off_after_sz(len_sz1, oa, ca, cb);
                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                      {
                                          cb: cb·_sz,
                                          ca: ca·_sz,
                                          ob: ob·_sz,
                                          before,
                                          oa: oa·_sz,
                                          after
                                      }
                                  },
                                _ => panic!("Incomplete pattern matching")
                            };
                        iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                        { before: bi·, after: rest }
                    };
                let
                mut
                r_it1:
                [iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;
                1]
                =
                    [it1_init; 1usize];
                let
                mut
                r_it2:
                [iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;
                1]
                =
                    [it2_init; 1usize];
                let mut r_acc: [i16; 1] = [0i16; 1usize];
                let mut r_cnt: [usize; 1] = [0usize; 1usize];
                let acc: i16 = (&r_acc)[0];
                let cnt: usize = (&r_cnt)[0];
                let mut cond: bool = cnt < len_sz && acc == 0i16;
                while
                cond
                {
                    let
                    i:
                    iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                    =
                        (&r_it1)[0];
                    let len_sz1: usize =
                        base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                            i.before
                        );
                    let
                    e1:
                    elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                    =
                        if len_sz1 == 0usize
                        { panic!("Pulse.Lib.Dv.unreachable") }
                        else
                        {
                            let
                            x:
                            elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                            =
                                match i.before
                                {
                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                    => panic!("Pulse.Lib.Dv.unreachable"),
                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                    { sr: s }
                                    =>
                                      {
                                          let
                                          x_val:
                                          cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                          =
                                              s[0];
                                          elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::EElement
                                          { _0: x_val }
                                      },
                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                    { ss: s }
                                    =>
                                      {
                                          let
                                          x_val:
                                          cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                          =
                                              s[0usize];
                                          elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::EElement
                                          { _0: x_val }
                                      },
                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                    { payload: pl, .. }
                                    =>
                                      {
                                          let mut pn: [usize; 1] = [0usize; 1usize];
                                          let mut poffset: [usize; 1] = [0usize; 1usize];
                                          let n1: usize = (&pn)[0];
                                          let mut cond0: bool = n1 > 0usize;
                                          while
                                          cond0
                                          {
                                              let n10: usize = (&pn)[0];
                                              let offset: usize = (&poffset)[0];
                                              let off1: usize = jump_raw_data_item(pl, offset);
                                              let offset·: usize = jump_raw_data_item(pl, off1);
                                              (&mut pn)[0] = n10.wrapping_sub(1usize);
                                              (&mut poffset)[0] = offset·;
                                              let n11: usize = (&pn)[0];
                                              cond0 = n11 > 0usize
                                          };
                                          let pos: usize = (&poffset)[0];
                                          let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                          let _pl_prefix: &[u8] = pl_p.0;
                                          let pl_suffix: &[u8] = pl_p.1;
                                          let off1: usize = jump_raw_data_item(pl_suffix, 0usize);
                                          let consumed_sz: usize =
                                              jump_raw_data_item(pl_suffix, off1);
                                          let pl_hd_p: (&[u8], &[u8]) =
                                              pl_suffix.split_at(consumed_sz);
                                          let pl_head: &[u8] = pl_hd_p.0;
                                          let _pl_rest: &[u8] = pl_hd_p.1;
                                          elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::ESerialized
                                          { _0: pl_head }
                                      },
                                    _ => panic!("Incomplete pattern matching")
                                };
                            if len_sz1 == 1usize
                            {
                                let total_sz1: usize =
                                    mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                        i.after
                                    );
                                let
                                it_new:
                                iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                =
                                    if total_sz1 == 0usize
                                    {
                                        iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        {
                                            before:
                                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                            after:
                                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                            {
                                                _0:
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                            }
                                        }
                                    }
                                    else
                                    {
                                        let
                                        mut
                                        r_node:
                                        [mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;
                                        1]
                                        =
                                            [i.after; 1usize];
                                        let mut r_off: [usize; 1] = [0usize; 1usize];
                                        let mut r_n: [usize; 1] = [total_sz1; 1usize];
                                        let mut pcontinue: [bool; 1] =
                                            [!
                                                uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                    i.after
                                                );
                                                1usize];
                                        while
                                        (&pcontinue)[0]
                                        {
                                            let
                                            node:
                                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                            =
                                                (&r_node)[0];
                                            let cur_off_v: usize = (&r_off)[0];
                                            let cur_n_v: usize = (&r_n)[0];
                                            match node
                                            {
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                { cb, ca, ob, before, oa, after }
                                                =>
                                                  {
                                                      let child_n_before: usize =
                                                          append_n_before_sz(cur_off_v, cur_n_v, cb);
                                                      if child_n_before > 0usize
                                                      {
                                                          let child_off_sz: usize =
                                                              append_off_before_sz(
                                                                  cur_off_v,
                                                                  ob,
                                                                  cb
                                                              );
                                                          let
                                                          ib:
                                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                          =
                                                              before[0];
                                                          (&mut r_node)[0] = ib;
                                                          (&mut r_off)[0] = child_off_sz;
                                                          (&mut r_n)[0] = child_n_before;
                                                          (&mut pcontinue)[0] =
                                                              !
                                                              uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                                  ib
                                                              )
                                                      }
                                                      else
                                                      {
                                                          let child_off_sz: usize =
                                                              append_off_after_sz(
                                                                  cur_off_v,
                                                                  oa,
                                                                  ca,
                                                                  cb
                                                              );
                                                          let child_n_sz: usize =
                                                              append_n_after_sz(
                                                                  cur_off_v,
                                                                  cur_n_v,
                                                                  cb
                                                              );
                                                          let
                                                          ia:
                                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                          =
                                                              after[0];
                                                          (&mut r_node)[0] = ia;
                                                          (&mut r_off)[0] = child_off_sz;
                                                          (&mut r_n)[0] = child_n_sz;
                                                          (&mut pcontinue)[0] =
                                                              !
                                                              uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                                  ia
                                                              )
                                                      }
                                                  },
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                { .. }
                                                => (),
                                                _ => panic!("Incomplete pattern matching")
                                            }
                                        };
                                        let
                                        node:
                                        mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        =
                                            (&r_node)[0];
                                        let cur_off_v: usize = (&r_off)[0];
                                        let cur_n_v: usize = (&r_n)[0];
                                        let
                                        res:
                                        (base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                                        usize)
                                        =
                                            match node
                                            {
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                { _0: bi }
                                                =>
                                                  {
                                                      let
                                                      bi·:
                                                      base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                      =
                                                          match bi
                                                          {
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                              =>
                                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                              { sr: s }
                                                              =>
                                                                if cur_n_v == 0usize
                                                                {
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                                }
                                                                else
                                                                {
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                                    { sr: s }
                                                                },
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                              { ss: s }
                                                              =>
                                                                {
                                                                    let
                                                                    s_pr:
                                                                    (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                                    =
                                                                        s.split_at(cur_off_v);
                                                                    let
                                                                    _s_prefix:
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                    =
                                                                        s_pr.0;
                                                                    let
                                                                    s_rest:
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                    =
                                                                        s_pr.1;
                                                                    let
                                                                    s_ms:
                                                                    (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                                    =
                                                                        s_rest.split_at(cur_n_v);
                                                                    let
                                                                    s_middle:
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                    =
                                                                        s_ms.0;
                                                                    let
                                                                    _s_suffix:
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                    =
                                                                        s_ms.1;
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                                    { ss: s_middle }
                                                                },
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                              { payload: pl, .. }
                                                              =>
                                                                {
                                                                    let mut pn: [usize; 1] =
                                                                        [cur_off_v; 1usize];
                                                                    let mut poffset: [usize; 1] =
                                                                        [0usize; 1usize];
                                                                    let n1: usize = (&pn)[0];
                                                                    let mut cond0: bool =
                                                                        n1 > 0usize;
                                                                    while
                                                                    cond0
                                                                    {
                                                                        let n10: usize = (&pn)[0];
                                                                        let offset: usize =
                                                                            (&poffset)[0];
                                                                        let off1: usize =
                                                                            jump_raw_data_item(
                                                                                pl,
                                                                                offset
                                                                            );
                                                                        let offset·: usize =
                                                                            jump_raw_data_item(
                                                                                pl,
                                                                                off1
                                                                            );
                                                                        (&mut pn)[0] =
                                                                            n10.wrapping_sub(1usize);
                                                                        (&mut poffset)[0] = offset·;
                                                                        let n11: usize = (&pn)[0];
                                                                        cond0 = n11 > 0usize
                                                                    };
                                                                    let pos: usize = (&poffset)[0];
                                                                    let pl_p: (&[u8], &[u8]) =
                                                                        pl.split_at(pos);
                                                                    let _pl_prefix: &[u8] = pl_p.0;
                                                                    let pl_suffix: &[u8] = pl_p.1;
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                                    {
                                                                        count: cur_n_v,
                                                                        payload: pl_suffix
                                                                    }
                                                                },
                                                              _ =>
                                                                panic!(
                                                                    "Incomplete pattern matching"
                                                                )
                                                          };
                                                      let len: usize =
                                                          base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                              bi·
                                                          );
                                                      (bi·,len)
                                                  },
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                { .. }
                                                => panic!("Pulse.Lib.Dv.unreachable"),
                                                _ => panic!("Incomplete pattern matching")
                                            };
                                        let
                                        bi·:
                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        =
                                            fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                                res
                                            );
                                        let len_sz2: usize =
                                            snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                                res
                                            );
                                        let rest_sz: usize = total_sz1.wrapping_sub(len_sz2);
                                        let
                                        rest:
                                        mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        =
                                            match i.after
                                            {
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                { _0: bi }
                                                =>
                                                  {
                                                      let
                                                      bi·1:
                                                      base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                      =
                                                          match bi
                                                          {
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                              =>
                                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                              { sr: s }
                                                              =>
                                                                if rest_sz == 0usize
                                                                {
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                                }
                                                                else
                                                                {
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                                    { sr: s }
                                                                },
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                              { ss: s }
                                                              =>
                                                                {
                                                                    let
                                                                    s_pr:
                                                                    (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                                    =
                                                                        s.split_at(len_sz2);
                                                                    let
                                                                    _s_prefix:
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                    =
                                                                        s_pr.0;
                                                                    let
                                                                    s_rest:
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                    =
                                                                        s_pr.1;
                                                                    let
                                                                    s_ms:
                                                                    (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                                    =
                                                                        s_rest.split_at(rest_sz);
                                                                    let
                                                                    s_middle:
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                    =
                                                                        s_ms.0;
                                                                    let
                                                                    _s_suffix:
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                    =
                                                                        s_ms.1;
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                                    { ss: s_middle }
                                                                },
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                              { payload: pl, .. }
                                                              =>
                                                                {
                                                                    let mut pn: [usize; 1] =
                                                                        [len_sz2; 1usize];
                                                                    let mut poffset: [usize; 1] =
                                                                        [0usize; 1usize];
                                                                    let n1: usize = (&pn)[0];
                                                                    let mut cond0: bool =
                                                                        n1 > 0usize;
                                                                    while
                                                                    cond0
                                                                    {
                                                                        let n10: usize = (&pn)[0];
                                                                        let offset: usize =
                                                                            (&poffset)[0];
                                                                        let off1: usize =
                                                                            jump_raw_data_item(
                                                                                pl,
                                                                                offset
                                                                            );
                                                                        let offset·: usize =
                                                                            jump_raw_data_item(
                                                                                pl,
                                                                                off1
                                                                            );
                                                                        (&mut pn)[0] =
                                                                            n10.wrapping_sub(1usize);
                                                                        (&mut poffset)[0] = offset·;
                                                                        let n11: usize = (&pn)[0];
                                                                        cond0 = n11 > 0usize
                                                                    };
                                                                    let pos: usize = (&poffset)[0];
                                                                    let pl_p: (&[u8], &[u8]) =
                                                                        pl.split_at(pos);
                                                                    let _pl_prefix: &[u8] = pl_p.0;
                                                                    let pl_suffix: &[u8] = pl_p.1;
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                                    {
                                                                        count: rest_sz,
                                                                        payload: pl_suffix
                                                                    }
                                                                },
                                                              _ =>
                                                                panic!(
                                                                    "Incomplete pattern matching"
                                                                )
                                                          };
                                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                      { _0: bi·1 }
                                                  },
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                { cb, ca, ob, before, oa, after }
                                                =>
                                                  {
                                                      let cb·_sz: usize =
                                                          append_n_before_sz(len_sz2, rest_sz, cb);
                                                      let ca·_sz: usize =
                                                          append_n_after_sz(len_sz2, rest_sz, cb);
                                                      let ob·_sz: usize =
                                                          append_off_before_sz(len_sz2, ob, cb);
                                                      let oa·_sz: usize =
                                                          append_off_after_sz(len_sz2, oa, ca, cb);
                                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                      {
                                                          cb: cb·_sz,
                                                          ca: ca·_sz,
                                                          ob: ob·_sz,
                                                          before,
                                                          oa: oa·_sz,
                                                          after
                                                      }
                                                  },
                                                _ => panic!("Incomplete pattern matching")
                                            };
                                        iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        { before: bi·, after: rest }
                                    };
                                (&mut r_it1)[0] = it_new;
                                x
                            }
                            else
                            {
                                let n_tail_sz: usize = len_sz1.wrapping_sub(1usize);
                                let
                                bi_tail:
                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                =
                                    match i.before
                                    {
                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                        =>
                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                        { sr: s }
                                        =>
                                          if n_tail_sz == 0usize
                                          {
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                          }
                                          else
                                          {
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                              { sr: s }
                                          },
                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                        { ss: s }
                                        =>
                                          {
                                              let
                                              s_pr:
                                              (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                              =
                                                  s.split_at(1usize);
                                              let
                                              _s_prefix:
                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                              =
                                                  s_pr.0;
                                              let
                                              s_rest:
                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                              =
                                                  s_pr.1;
                                              let
                                              s_ms:
                                              (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                              =
                                                  s_rest.split_at(n_tail_sz);
                                              let
                                              s_middle:
                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                              =
                                                  s_ms.0;
                                              let
                                              _s_suffix:
                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                              =
                                                  s_ms.1;
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                              { ss: s_middle }
                                          },
                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                        { payload: pl, .. }
                                        =>
                                          {
                                              let mut pn: [usize; 1] = [1usize; 1usize];
                                              let mut poffset: [usize; 1] = [0usize; 1usize];
                                              let n1: usize = (&pn)[0];
                                              let mut cond0: bool = n1 > 0usize;
                                              while
                                              cond0
                                              {
                                                  let n10: usize = (&pn)[0];
                                                  let offset: usize = (&poffset)[0];
                                                  let off1: usize = jump_raw_data_item(pl, offset);
                                                  let offset·: usize =
                                                      jump_raw_data_item(pl, off1);
                                                  (&mut pn)[0] = n10.wrapping_sub(1usize);
                                                  (&mut poffset)[0] = offset·;
                                                  let n11: usize = (&pn)[0];
                                                  cond0 = n11 > 0usize
                                              };
                                              let pos: usize = (&poffset)[0];
                                              let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                              let _pl_prefix: &[u8] = pl_p.0;
                                              let pl_suffix: &[u8] = pl_p.1;
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                              { count: n_tail_sz, payload: pl_suffix }
                                          },
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                let
                                it_new:
                                iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                =
                                    iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                    { before: bi_tail, after: i.after };
                                (&mut r_it1)[0] = it_new;
                                x
                            }
                        };
                    let
                    i0:
                    iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                    =
                        (&r_it2)[0];
                    let len_sz10: usize =
                        base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                            i0.before
                        );
                    let
                    e2:
                    elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                    =
                        if len_sz10 == 0usize
                        { panic!("Pulse.Lib.Dv.unreachable") }
                        else
                        {
                            let
                            x:
                            elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                            =
                                match i0.before
                                {
                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                    => panic!("Pulse.Lib.Dv.unreachable"),
                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                    { sr: s }
                                    =>
                                      {
                                          let
                                          x_val:
                                          cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                          =
                                              s[0];
                                          elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::EElement
                                          { _0: x_val }
                                      },
                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                    { ss: s }
                                    =>
                                      {
                                          let
                                          x_val:
                                          cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                          =
                                              s[0usize];
                                          elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::EElement
                                          { _0: x_val }
                                      },
                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                    { payload: pl, .. }
                                    =>
                                      {
                                          let mut pn: [usize; 1] = [0usize; 1usize];
                                          let mut poffset: [usize; 1] = [0usize; 1usize];
                                          let n1: usize = (&pn)[0];
                                          let mut cond0: bool = n1 > 0usize;
                                          while
                                          cond0
                                          {
                                              let n10: usize = (&pn)[0];
                                              let offset: usize = (&poffset)[0];
                                              let off1: usize = jump_raw_data_item(pl, offset);
                                              let offset·: usize = jump_raw_data_item(pl, off1);
                                              (&mut pn)[0] = n10.wrapping_sub(1usize);
                                              (&mut poffset)[0] = offset·;
                                              let n11: usize = (&pn)[0];
                                              cond0 = n11 > 0usize
                                          };
                                          let pos: usize = (&poffset)[0];
                                          let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                          let _pl_prefix: &[u8] = pl_p.0;
                                          let pl_suffix: &[u8] = pl_p.1;
                                          let off1: usize = jump_raw_data_item(pl_suffix, 0usize);
                                          let consumed_sz: usize =
                                              jump_raw_data_item(pl_suffix, off1);
                                          let pl_hd_p: (&[u8], &[u8]) =
                                              pl_suffix.split_at(consumed_sz);
                                          let pl_head: &[u8] = pl_hd_p.0;
                                          let _pl_rest: &[u8] = pl_hd_p.1;
                                          elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::ESerialized
                                          { _0: pl_head }
                                      },
                                    _ => panic!("Incomplete pattern matching")
                                };
                            if len_sz10 == 1usize
                            {
                                let total_sz1: usize =
                                    mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                        i0.after
                                    );
                                let
                                it_new:
                                iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                =
                                    if total_sz1 == 0usize
                                    {
                                        iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        {
                                            before:
                                            base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                            after:
                                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                            {
                                                _0:
                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                            }
                                        }
                                    }
                                    else
                                    {
                                        let
                                        mut
                                        r_node:
                                        [mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw;
                                        1]
                                        =
                                            [i0.after; 1usize];
                                        let mut r_off: [usize; 1] = [0usize; 1usize];
                                        let mut r_n: [usize; 1] = [total_sz1; 1usize];
                                        let mut pcontinue: [bool; 1] =
                                            [!
                                                uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                    i0.after
                                                );
                                                1usize];
                                        while
                                        (&pcontinue)[0]
                                        {
                                            let
                                            node:
                                            mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                            =
                                                (&r_node)[0];
                                            let cur_off_v: usize = (&r_off)[0];
                                            let cur_n_v: usize = (&r_n)[0];
                                            match node
                                            {
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                { cb, ca, ob, before, oa, after }
                                                =>
                                                  {
                                                      let child_n_before: usize =
                                                          append_n_before_sz(cur_off_v, cur_n_v, cb);
                                                      if child_n_before > 0usize
                                                      {
                                                          let child_off_sz: usize =
                                                              append_off_before_sz(
                                                                  cur_off_v,
                                                                  ob,
                                                                  cb
                                                              );
                                                          let
                                                          ib:
                                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                          =
                                                              before[0];
                                                          (&mut r_node)[0] = ib;
                                                          (&mut r_off)[0] = child_off_sz;
                                                          (&mut r_n)[0] = child_n_before;
                                                          (&mut pcontinue)[0] =
                                                              !
                                                              uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                                  ib
                                                              )
                                                      }
                                                      else
                                                      {
                                                          let child_off_sz: usize =
                                                              append_off_after_sz(
                                                                  cur_off_v,
                                                                  oa,
                                                                  ca,
                                                                  cb
                                                              );
                                                          let child_n_sz: usize =
                                                              append_n_after_sz(
                                                                  cur_off_v,
                                                                  cur_n_v,
                                                                  cb
                                                              );
                                                          let
                                                          ia:
                                                          mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                          =
                                                              after[0];
                                                          (&mut r_node)[0] = ia;
                                                          (&mut r_off)[0] = child_off_sz;
                                                          (&mut r_n)[0] = child_n_sz;
                                                          (&mut pcontinue)[0] =
                                                              !
                                                              uu___is_Base__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                                  ia
                                                              )
                                                      }
                                                  },
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                { .. }
                                                => (),
                                                _ => panic!("Incomplete pattern matching")
                                            }
                                        };
                                        let
                                        node:
                                        mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        =
                                            (&r_node)[0];
                                        let cur_off_v: usize = (&r_off)[0];
                                        let cur_n_v: usize = (&r_n)[0];
                                        let
                                        res:
                                        (base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw,
                                        usize)
                                        =
                                            match node
                                            {
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                { _0: bi }
                                                =>
                                                  {
                                                      let
                                                      bi·:
                                                      base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                      =
                                                          match bi
                                                          {
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                              =>
                                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                              { sr: s }
                                                              =>
                                                                if cur_n_v == 0usize
                                                                {
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                                }
                                                                else
                                                                {
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                                    { sr: s }
                                                                },
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                              { ss: s }
                                                              =>
                                                                {
                                                                    let
                                                                    s_pr:
                                                                    (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                                    =
                                                                        s.split_at(cur_off_v);
                                                                    let
                                                                    _s_prefix:
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                    =
                                                                        s_pr.0;
                                                                    let
                                                                    s_rest:
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                    =
                                                                        s_pr.1;
                                                                    let
                                                                    s_ms:
                                                                    (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                                    =
                                                                        s_rest.split_at(cur_n_v);
                                                                    let
                                                                    s_middle:
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                    =
                                                                        s_ms.0;
                                                                    let
                                                                    _s_suffix:
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                    =
                                                                        s_ms.1;
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                                    { ss: s_middle }
                                                                },
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                              { payload: pl, .. }
                                                              =>
                                                                {
                                                                    let mut pn: [usize; 1] =
                                                                        [cur_off_v; 1usize];
                                                                    let mut poffset: [usize; 1] =
                                                                        [0usize; 1usize];
                                                                    let n1: usize = (&pn)[0];
                                                                    let mut cond0: bool =
                                                                        n1 > 0usize;
                                                                    while
                                                                    cond0
                                                                    {
                                                                        let n10: usize = (&pn)[0];
                                                                        let offset: usize =
                                                                            (&poffset)[0];
                                                                        let off1: usize =
                                                                            jump_raw_data_item(
                                                                                pl,
                                                                                offset
                                                                            );
                                                                        let offset·: usize =
                                                                            jump_raw_data_item(
                                                                                pl,
                                                                                off1
                                                                            );
                                                                        (&mut pn)[0] =
                                                                            n10.wrapping_sub(1usize);
                                                                        (&mut poffset)[0] = offset·;
                                                                        let n11: usize = (&pn)[0];
                                                                        cond0 = n11 > 0usize
                                                                    };
                                                                    let pos: usize = (&poffset)[0];
                                                                    let pl_p: (&[u8], &[u8]) =
                                                                        pl.split_at(pos);
                                                                    let _pl_prefix: &[u8] = pl_p.0;
                                                                    let pl_suffix: &[u8] = pl_p.1;
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                                    {
                                                                        count: cur_n_v,
                                                                        payload: pl_suffix
                                                                    }
                                                                },
                                                              _ =>
                                                                panic!(
                                                                    "Incomplete pattern matching"
                                                                )
                                                          };
                                                      let len: usize =
                                                          base_mixed_list_length__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                              bi·
                                                          );
                                                      (bi·,len)
                                                  },
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                { .. }
                                                => panic!("Pulse.Lib.Dv.unreachable"),
                                                _ => panic!("Incomplete pattern matching")
                                            };
                                        let
                                        bi·:
                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        =
                                            fst__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                                res
                                            );
                                        let len_sz2: usize =
                                            snd__LowParse_PulseParse_Iterator_Type_base_mixed_list·CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry·CBOR_Pulse_Raw_EverParse_Type_cbor_raw_size_t(
                                                res
                                            );
                                        let rest_sz: usize = total_sz1.wrapping_sub(len_sz2);
                                        let
                                        rest:
                                        mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        =
                                            match i0.after
                                            {
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                { _0: bi }
                                                =>
                                                  {
                                                      let
                                                      bi·1:
                                                      base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                                      =
                                                          match bi
                                                          {
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                              =>
                                                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                              { sr: s }
                                                              =>
                                                                if rest_sz == 0usize
                                                                {
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                                                }
                                                                else
                                                                {
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                                                    { sr: s }
                                                                },
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                              { ss: s }
                                                              =>
                                                                {
                                                                    let
                                                                    s_pr:
                                                                    (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                                    =
                                                                        s.split_at(len_sz2);
                                                                    let
                                                                    _s_prefix:
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                    =
                                                                        s_pr.0;
                                                                    let
                                                                    s_rest:
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                    =
                                                                        s_pr.1;
                                                                    let
                                                                    s_ms:
                                                                    (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                                                    =
                                                                        s_rest.split_at(rest_sz);
                                                                    let
                                                                    s_middle:
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                    =
                                                                        s_ms.0;
                                                                    let
                                                                    _s_suffix:
                                                                    &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                                                    =
                                                                        s_ms.1;
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                                                    { ss: s_middle }
                                                                },
                                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                              { payload: pl, .. }
                                                              =>
                                                                {
                                                                    let mut pn: [usize; 1] =
                                                                        [len_sz2; 1usize];
                                                                    let mut poffset: [usize; 1] =
                                                                        [0usize; 1usize];
                                                                    let n1: usize = (&pn)[0];
                                                                    let mut cond0: bool =
                                                                        n1 > 0usize;
                                                                    while
                                                                    cond0
                                                                    {
                                                                        let n10: usize = (&pn)[0];
                                                                        let offset: usize =
                                                                            (&poffset)[0];
                                                                        let off1: usize =
                                                                            jump_raw_data_item(
                                                                                pl,
                                                                                offset
                                                                            );
                                                                        let offset·: usize =
                                                                            jump_raw_data_item(
                                                                                pl,
                                                                                off1
                                                                            );
                                                                        (&mut pn)[0] =
                                                                            n10.wrapping_sub(1usize);
                                                                        (&mut poffset)[0] = offset·;
                                                                        let n11: usize = (&pn)[0];
                                                                        cond0 = n11 > 0usize
                                                                    };
                                                                    let pos: usize = (&poffset)[0];
                                                                    let pl_p: (&[u8], &[u8]) =
                                                                        pl.split_at(pos);
                                                                    let _pl_prefix: &[u8] = pl_p.0;
                                                                    let pl_suffix: &[u8] = pl_p.1;
                                                                    base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                                                    {
                                                                        count: rest_sz,
                                                                        payload: pl_suffix
                                                                    }
                                                                },
                                                              _ =>
                                                                panic!(
                                                                    "Incomplete pattern matching"
                                                                )
                                                          };
                                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Base
                                                      { _0: bi·1 }
                                                  },
                                                mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                { cb, ca, ob, before, oa, after }
                                                =>
                                                  {
                                                      let cb·_sz: usize =
                                                          append_n_before_sz(len_sz2, rest_sz, cb);
                                                      let ca·_sz: usize =
                                                          append_n_after_sz(len_sz2, rest_sz, cb);
                                                      let ob·_sz: usize =
                                                          append_off_before_sz(len_sz2, ob, cb);
                                                      let oa·_sz: usize =
                                                          append_off_after_sz(len_sz2, oa, ca, cb);
                                                      mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Append
                                                      {
                                                          cb: cb·_sz,
                                                          ca: ca·_sz,
                                                          ob: ob·_sz,
                                                          before,
                                                          oa: oa·_sz,
                                                          after
                                                      }
                                                  },
                                                _ => panic!("Incomplete pattern matching")
                                            };
                                        iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        { before: bi·, after: rest }
                                    };
                                (&mut r_it2)[0] = it_new;
                                x
                            }
                            else
                            {
                                let n_tail_sz: usize = len_sz10.wrapping_sub(1usize);
                                let
                                bi_tail:
                                base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                =
                                    match i0.before
                                    {
                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                        =>
                                          base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty,
                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                        { sr: s }
                                        =>
                                          if n_tail_sz == 0usize
                                          {
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Empty
                                          }
                                          else
                                          {
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Singleton
                                              { sr: s }
                                          },
                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                        { ss: s }
                                        =>
                                          {
                                              let
                                              s_pr:
                                              (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                              =
                                                  s.split_at(1usize);
                                              let
                                              _s_prefix:
                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                              =
                                                  s_pr.0;
                                              let
                                              s_rest:
                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                              =
                                                  s_pr.1;
                                              let
                                              s_ms:
                                              (&[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                                              =
                                                  s_rest.split_at(n_tail_sz);
                                              let
                                              s_middle:
                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                              =
                                                  s_ms.0;
                                              let
                                              _s_suffix:
                                              &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
                                              =
                                                  s_ms.1;
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Slice
                                              { ss: s_middle }
                                          },
                                        base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                        { payload: pl, .. }
                                        =>
                                          {
                                              let mut pn: [usize; 1] = [1usize; 1usize];
                                              let mut poffset: [usize; 1] = [0usize; 1usize];
                                              let n1: usize = (&pn)[0];
                                              let mut cond0: bool = n1 > 0usize;
                                              while
                                              cond0
                                              {
                                                  let n10: usize = (&pn)[0];
                                                  let offset: usize = (&poffset)[0];
                                                  let off1: usize = jump_raw_data_item(pl, offset);
                                                  let offset·: usize =
                                                      jump_raw_data_item(pl, off1);
                                                  (&mut pn)[0] = n10.wrapping_sub(1usize);
                                                  (&mut poffset)[0] = offset·;
                                                  let n11: usize = (&pn)[0];
                                                  cond0 = n11 > 0usize
                                              };
                                              let pos: usize = (&poffset)[0];
                                              let pl_p: (&[u8], &[u8]) = pl.split_at(pos);
                                              let _pl_prefix: &[u8] = pl_p.0;
                                              let pl_suffix: &[u8] = pl_p.1;
                                              base_mixed_list__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::Serialized
                                              { count: n_tail_sz, payload: pl_suffix }
                                          },
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                let
                                it_new:
                                iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                =
                                    iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                    { before: bi_tail, after: i0.after };
                                (&mut r_it2)[0] = it_new;
                                x
                            }
                        };
                    let old_cnt: usize = (&r_cnt)[0];
                    match e1
                    {
                        elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::EElement
                        { _0: entry1 }
                        =>
                          match e2
                          {
                              elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::EElement
                              { _0: entry2 }
                              =>
                                {
                                    let ck: i16 =
                                        impl_cbor_compare_fuel(
                                            entry1.cbor_map_entry_key,
                                            entry2.cbor_map_entry_key
                                        );
                                    if ck == 0i16
                                    {
                                        let cv: i16 =
                                            impl_cbor_compare_fuel(
                                                entry1.cbor_map_entry_value,
                                                entry2.cbor_map_entry_value
                                            );
                                        (&mut r_acc)[0] = cv;
                                        (&mut r_cnt)[0] = old_cnt.wrapping_add(1usize)
                                    }
                                    else
                                    {
                                        (&mut r_acc)[0] = ck;
                                        (&mut r_cnt)[0] = old_cnt.wrapping_add(1usize)
                                    }
                                },
                              elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::ESerialized
                              { _0: s2 }
                              =>
                                {
                                    let off1: usize = jump_raw_data_item(s2, 0usize);
                                    let s·: (&[u8], &[u8]) = s2.split_at(off1);
                                    let _letpattern: (&[u8], &[u8]) =
                                        {
                                            let s1: &[u8] = s·.0;
                                            let s21: &[u8] = s·.1;
                                            (s1,s21)
                                        };
                                    let pair: (cbor_raw, cbor_raw) =
                                        {
                                            let input1: &[u8] = _letpattern.0;
                                            let input2: &[u8] = _letpattern.1;
                                            let res1: cbor_raw = cbor_raw_read_fuel(input1);
                                            let res2: cbor_raw = cbor_raw_read_fuel(input2);
                                            (res1,res2)
                                        };
                                    let
                                    entry2: cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                    =
                                        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        {
                                            cbor_map_entry_key:
                                            fst__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                pair
                                            ),
                                            cbor_map_entry_value:
                                            snd__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                pair
                                            )
                                        };
                                    let ck: i16 =
                                        impl_cbor_compare_fuel(
                                            entry1.cbor_map_entry_key,
                                            entry2.cbor_map_entry_key
                                        );
                                    if ck == 0i16
                                    {
                                        let cv: i16 =
                                            impl_cbor_compare_fuel(
                                                entry1.cbor_map_entry_value,
                                                entry2.cbor_map_entry_value
                                            );
                                        (&mut r_acc)[0] = cv;
                                        (&mut r_cnt)[0] = old_cnt.wrapping_add(1usize)
                                    }
                                    else
                                    {
                                        (&mut r_acc)[0] = ck;
                                        (&mut r_cnt)[0] = old_cnt.wrapping_add(1usize)
                                    }
                                },
                              _ => panic!("Incomplete pattern matching")
                          },
                        elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::ESerialized
                        { _0: s1 }
                        =>
                          match e2
                          {
                              elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::EElement
                              { _0: entry2 }
                              =>
                                {
                                    let off1: usize = jump_raw_data_item(s1, 0usize);
                                    let s·: (&[u8], &[u8]) = s1.split_at(off1);
                                    let _letpattern: (&[u8], &[u8]) =
                                        {
                                            let s11: &[u8] = s·.0;
                                            let s2: &[u8] = s·.1;
                                            (s11,s2)
                                        };
                                    let pair: (cbor_raw, cbor_raw) =
                                        {
                                            let input1: &[u8] = _letpattern.0;
                                            let input2: &[u8] = _letpattern.1;
                                            let res1: cbor_raw = cbor_raw_read_fuel(input1);
                                            let res2: cbor_raw = cbor_raw_read_fuel(input2);
                                            (res1,res2)
                                        };
                                    let
                                    entry1: cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                    =
                                        cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
                                        {
                                            cbor_map_entry_key:
                                            fst__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                pair
                                            ),
                                            cbor_map_entry_value:
                                            snd__CBOR_Pulse_Raw_EverParse_Type_cbor_raw_CBOR_Pulse_Raw_EverParse_Type_cbor_raw(
                                                pair
                                            )
                                        };
                                    let ck: i16 =
                                        impl_cbor_compare_fuel(
                                            entry1.cbor_map_entry_key,
                                            entry2.cbor_map_entry_key
                                        );
                                    if ck == 0i16
                                    {
                                        let cv: i16 =
                                            impl_cbor_compare_fuel(
                                                entry1.cbor_map_entry_value,
                                                entry2.cbor_map_entry_value
                                            );
                                        (&mut r_acc)[0] = cv;
                                        (&mut r_cnt)[0] = old_cnt.wrapping_add(1usize)
                                    }
                                    else
                                    {
                                        (&mut r_acc)[0] = ck;
                                        (&mut r_cnt)[0] = old_cnt.wrapping_add(1usize)
                                    }
                                },
                              elt_or_serialized__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw::ESerialized
                              { _0: s2 }
                              =>
                                {
                                    let pair_res: i16 = lex_compare_bytes(s1, s2);
                                    (&mut r_acc)[0] = pair_res;
                                    (&mut r_cnt)[0] = old_cnt.wrapping_add(1usize)
                                },
                              _ => panic!("Incomplete pattern matching")
                          },
                        _ => panic!("Incomplete pattern matching")
                    };
                    let acc0: i16 = (&r_acc)[0];
                    let cnt0: usize = (&r_cnt)[0];
                    cond = cnt0 < len_sz && acc0 == 0i16
                };
                (&r_acc)[0]
            }
            else
            { cl }
        }
        else
        {
            let sv1: u8 =
                match x1
                {
                    cbor_raw::CBOR_Case_Simple { v } => v,
                    _ => panic!("Incomplete pattern matching")
                };
            let sv2: u8 =
                match x2
                {
                    cbor_raw::CBOR_Case_Simple { v } => v,
                    _ => panic!("Incomplete pattern matching")
                };
            impl_uint8_compare(sv1, sv2)
        }
    }
    else
    { c }
}

pub(crate) fn impl_cbor_compare(x1: cbor_raw, x2: cbor_raw) -> i16
{ impl_cbor_compare_fuel(x1, x2) }

pub(crate) fn cbor_det_serialize_slice(x: cbor_raw, output: &mut [u8]) -> usize
{ cbor_serialize(x, output) }

pub(crate) fn cbor_raw_sort_aux(
    a: &mut [cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]
) ->
    bool
{
    let len: usize = a.len();
    if len < 2usize
    { true }
    else
    {
        let len_half: usize = len.wrapping_div(2usize);
        let mi: usize = len_half;
        let
        _letpattern:
        (&mut [cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
        &mut [cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
        =
            a.split_at_mut(mi);
        let a1: &mut [cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw] = _letpattern.0;
        let a2: &mut [cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw] = _letpattern.1;
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
                    let x1: cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw = a[i10];
                    let i20: usize = (&pi2)[0];
                    let x2: cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw = a[i20];
                    let comp: i16 = impl_cbor_compare(x1.cbor_map_entry_key, x2.cbor_map_entry_key);
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
                        let
                        _letpattern1:
                        (&mut [cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                        &mut [cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                        =
                            a.split_at_mut(i2·);
                        let ac01: &mut [cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw] =
                            _letpattern1.0;
                        let _ac2: &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw] =
                            _letpattern1.1;
                        let
                        _letpattern2:
                        (&mut [cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw],
                        &mut [cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw])
                        =
                            ac01.split_at_mut(i10);
                        let _ac: &[cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw] =
                            _letpattern2.0;
                        let ac1: &mut [cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw] =
                            _letpattern2.1;
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
                                let save: cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                                    ac1[i];
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
                                    let x: cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw =
                                        ac1[idx·];
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
                (&pres)[0]
            }
        }
    }
}

pub(crate) fn cbor_raw_sort(a: &mut [cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw]) ->
    bool
{ cbor_raw_sort_aux(a) }

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

pub fn uu___is_CBOR_Case_Invalid(projectee: cbor_raw) -> bool
{ match projectee { cbor_raw::CBOR_Case_Invalid => true, _ => false } }

pub fn uu___is_CBOR_Case_Int(projectee: cbor_raw) -> bool
{ match projectee { cbor_raw::CBOR_Case_Int { .. } => true, _ => false } }

pub fn uu___is_CBOR_Case_Simple(projectee: cbor_raw) -> bool
{ match projectee { cbor_raw::CBOR_Case_Simple { .. } => true, _ => false } }

pub fn uu___is_CBOR_Case_String(projectee: cbor_raw) -> bool
{ match projectee { cbor_raw::CBOR_Case_String { .. } => true, _ => false } }

pub fn uu___is_CBOR_Case_Tagged(projectee: cbor_raw) -> bool
{ match projectee { cbor_raw::CBOR_Case_Tagged { .. } => true, _ => false } }

pub fn uu___is_CBOR_Case_Tagged_Serialized(projectee: cbor_raw) -> bool
{ match projectee { cbor_raw::CBOR_Case_Tagged_Serialized { .. } => true, _ => false } }

pub fn uu___is_CBOR_Case_Array(projectee: cbor_raw) -> bool
{ match projectee { cbor_raw::CBOR_Case_Array { .. } => true, _ => false } }

pub fn uu___is_CBOR_Case_Map(projectee: cbor_raw) -> bool
{ match projectee { cbor_raw::CBOR_Case_Map { .. } => true, _ => false } }

pub type cbor_det_t <'a> = cbor_raw <'a>;

pub type cbor_det_map_entry_t <'a> =
cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>;

pub type cbor_det_array_iterator_t <'a> =
iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_raw <'a>;

pub type cbor_det_map_iterator_t <'a> =
iterator__CBOR_Pulse_Raw_EverParse_Type_cbor_map_entry__CBOR_Pulse_Raw_EverParse_Type_cbor_raw
<'a>;

pub fn dummy_cbor_det_t <'a>() -> cbor_raw <'a> { cbor_raw::CBOR_Case_Simple { v: 0u8 } }
