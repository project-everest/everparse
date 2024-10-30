#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

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

#[derive(PartialEq, Clone, Copy)] pub struct raw_uint64 { pub size: u8, pub value: u64 }

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
    LongArgumentOther { a: u8 }
}

#[derive(PartialEq, Clone, Copy)]
struct header
{ pub fst: initial_byte_t, pub snd: long_argument }

fn argument_as_uint64(x: long_argument) -> u64
{
    match x
    {
        long_argument::LongArgumentU8 { v } => raw_uint64 { size: 1u8, value: v as u64 },
        long_argument::LongArgumentU16 { v } => raw_uint64 { size: 2u8, value: v as u64 },
        long_argument::LongArgumentU32 { v } => raw_uint64 { size: 3u8, value: v as u64 },
        long_argument::LongArgumentU64 { v } => raw_uint64 { size: 4u8, value: v },
        long_argument::LongArgumentOther { a: v } => raw_uint64 { size: 0u8, value: v as u64 },
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
            snd: long_argument::LongArgumentOther { a: x.value as u8 }
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
            snd: long_argument::LongArgumentOther { a: x }
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

type cbor_raw_serialized_iterator <'a> = &'a [u8];

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
    let res0: usize = res2;
    res0
}

fn size_header(x: header, out: &mut [usize]) -> bool
{
    let xh1: initial_byte_t =
        dfst__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
    let capacity: usize = out[0];
    let res: bool =
        if capacity < 1usize
        { false }
        else
        {
            out[0] = capacity.wrapping_sub(1usize);
            true
        };
    let res1: bool = res;
    if res1
    {
        let x2·: long_argument =
            dsnd__CBOR_Spec_Raw_EverParse_initial_byte_t_CBOR_Spec_Raw_EverParse_long_argument(x);
        crate::lowstar::ignore::ignore::<long_argument>(x2·);
        let res0: bool =
            if xh1.additional_info == additional_info_long_argument_8_bits
            {
                let capacity0: usize = out[0];
                let res0: bool =
                    if capacity0 < 1usize
                    { false }
                    else
                    {
                        out[0] = capacity0.wrapping_sub(1usize);
                        true
                    };
                res0
            }
            else if xh1.additional_info == additional_info_long_argument_16_bits
            {
                let capacity0: usize = out[0];
                let res0: bool =
                    if capacity0 < 2usize
                    { false }
                    else
                    {
                        out[0] = capacity0.wrapping_sub(2usize);
                        true
                    };
                res0
            }
            else if xh1.additional_info == additional_info_long_argument_32_bits
            {
                let capacity0: usize = out[0];
                let res0: bool =
                    if capacity0 < 4usize
                    { false }
                    else
                    {
                        out[0] = capacity0.wrapping_sub(4usize);
                        true
                    };
                res0
            }
            else if xh1.additional_info == additional_info_long_argument_64_bits
            {
                let capacity0: usize = out[0];
                let res0: bool =
                    if capacity0 < 8usize
                    { false }
                    else
                    {
                        out[0] = capacity0.wrapping_sub(8usize);
                        true
                    };
                res0
            }
            else
            { true };
        let res2: bool = res0;
        res2
    }
    else
    { false }
}

#[derive(PartialEq, Clone, Copy)]
pub struct cbor_int
{ pub cbor_int_type: u8, pub cbor_int_size: u8, pub cbor_int_value: u64 }

#[derive(PartialEq)]
pub struct cbor_string <'a>
{ pub cbor_string_type: u8, pub cbor_string_size: u8, pub cbor_string_ptr: &'a mut [u8] }

#[derive(PartialEq)]
pub struct cbor_tagged <'a>
{ pub cbor_tagged_tag: raw_uint64, pub cbor_tagged_ptr: &'a [cbor_raw <'a>] }

#[derive(PartialEq)]
pub struct cbor_array <'a>
{ pub cbor_array_length: raw_uint64, pub cbor_array_ptr: &'a [cbor_raw <'a>] }

#[derive(PartialEq)]
pub struct cbor_map <'a>
{ pub cbor_map_length: raw_uint64, pub cbor_map_ptr: &'a [cbor_map_entry <'a>] }

#[derive(PartialEq)]
pub struct cbor_serialized <'a>
{ pub cbor_serialized_header: raw_uint64, pub cbor_serialized_payload: &'a mut [u8] }

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

#[derive(PartialEq)]
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

fn cbor_raw_get_header <'a>(xl: cbor_raw <'a>) -> header
{
    if match xl { cbor_raw::CBOR_Case_Int { .. } => true, _ => false }
    {
        let c·: cbor_int =
            match xl
            { cbor_raw::CBOR_Case_Int { v } => v, _ => panic!("Incomplete pattern matching") };
        let ty: u8 = c·.cbor_int_type;
        let c·0: cbor_int =
            match xl
            { cbor_raw::CBOR_Case_Int { v } => v, _ => panic!("Incomplete pattern matching") };
        let v: raw_uint64 = raw_uint64 { size: c·0.cbor_int_size, value: c·0.cbor_int_value };
        raw_uint64_as_argument(ty, v)
    }
    else if match xl { cbor_raw::CBOR_Case_String { .. } => true, _ => false }
    {
        let c·: cbor_string =
            match xl
            { cbor_raw::CBOR_Case_String { v } => v, _ => panic!("Incomplete pattern matching") };
        let ty: u8 = c·.cbor_string_type;
        let c·0: cbor_string =
            match xl
            { cbor_raw::CBOR_Case_String { v } => v, _ => panic!("Incomplete pattern matching") };
        let res: raw_uint64 =
            raw_uint64 { size: c·0.cbor_string_size, value: c·0.cbor_string_ptr.len() as u64 };
        let len: raw_uint64 = res;
        raw_uint64_as_argument(ty, len)
    }
    else
    {
        let a: bool = match xl { cbor_raw::CBOR_Case_Tagged { .. } => true, _ => false };
        let ite: bool =
            if a
            { true }
            else
            { match xl { cbor_raw::CBOR_Case_Serialized_Tagged { .. } => true, _ => false } };
        if ite
        {
            let tag: raw_uint64 =
                match xl
                {
                    cbor_raw::CBOR_Case_Tagged { v: c· } => c·.cbor_tagged_tag,
                    cbor_raw::CBOR_Case_Serialized_Tagged { v: c· } => c·.cbor_serialized_header,
                    _ => panic!("Incomplete pattern matching")
                };
            raw_uint64_as_argument(cbor_major_type_tagged, tag)
        }
        else
        {
            let a0: bool = match xl { cbor_raw::CBOR_Case_Array { .. } => true, _ => false };
            let ite0: bool =
                if a0
                { true }
                else
                { match xl { cbor_raw::CBOR_Case_Serialized_Array { .. } => true, _ => false } };
            if ite0
            {
                let len: raw_uint64 =
                    match xl
                    {
                        cbor_raw::CBOR_Case_Array { v: c· } => c·.cbor_array_length,
                        cbor_raw::CBOR_Case_Serialized_Array { v: c· } =>
                          c·.cbor_serialized_header,
                        _ => panic!("Incomplete pattern matching")
                    };
                raw_uint64_as_argument(cbor_major_type_array, len)
            }
            else
            {
                let a1: bool = match xl { cbor_raw::CBOR_Case_Map { .. } => true, _ => false };
                let ite1: bool =
                    if a1
                    { true }
                    else
                    { match xl { cbor_raw::CBOR_Case_Serialized_Map { .. } => true, _ => false } };
                if ite1
                {
                    let len: raw_uint64 =
                        match xl
                        {
                            cbor_raw::CBOR_Case_Map { v: c· } => c·.cbor_map_length,
                            cbor_raw::CBOR_Case_Serialized_Map { v: c· } =>
                              c·.cbor_serialized_header,
                            _ => panic!("Incomplete pattern matching")
                        };
                    raw_uint64_as_argument(cbor_major_type_map, len)
                }
                else
                {
                    let v: u8 =
                        match xl
                        {
                            cbor_raw::CBOR_Case_Simple { v } => v,
                            _ => panic!("Incomplete pattern matching")
                        };
                    simple_value_as_argument(v)
                }
            }
        }
    }
}

fn cbor_raw_with_perm_get_header <'a>(xl: cbor_raw <'a>) -> header
{
    let res: header = cbor_raw_get_header(xl);
    res
}

#[derive(PartialEq, Clone, Copy)]
enum option__LowParse_Pulse_Base_with_perm··CBOR_Pulse_Raw_Type_cbor_raw·_tags
{
    None,
    Some
}

#[derive(PartialEq)]
enum option__LowParse_Pulse_Base_with_perm··CBOR_Pulse_Raw_Type_cbor_raw· <'a>
{
    None,
    Some { v: &'a [cbor_raw <'a>] }
}

#[derive(PartialEq)]
enum option__LowParse_Pulse_Base_with_perm··CBOR_Pulse_Raw_Type_cbor_map_entry· <'a>
{
    None,
    Some { v: &'a [cbor_map_entry <'a>] }
}

#[derive(PartialEq)]
struct __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t <'a>
{ pub fst: &'a mut [u8], pub snd: &'a mut [u8] }

#[derive(PartialEq)]
pub struct cbor_map_entry <'a>
{ pub cbor_map_entry_key: cbor_raw <'a>, pub cbor_map_entry_value: cbor_raw <'a> }

pub(crate) fn ser· <'a>(x·: cbor_raw <'a>, out: &'a mut [u8], offset: usize) -> usize
{
    let res: header = cbor_raw_with_perm_get_header(x·);
    let xh1: header = res;
    let res1: usize = write_header(xh1, out, offset);
    let b: initial_byte_t = xh1.fst;
    let res2: usize =
        if
        b.major_type == cbor_major_type_byte_string || b.major_type == cbor_major_type_text_string
        {
            let c·: cbor_string =
                match x·
                {
                    cbor_raw::CBOR_Case_String { v: v1 } => v1,
                    _ => panic!("Incomplete pattern matching")
                };
            let x2·: &mut [u8] = c·.cbor_string_ptr;
            let length: usize = x2·.len();
            let sp1: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                {
                    let actual_pair: (&mut [u8], &mut [u8]) = out.split_at_mut(res1);
                    __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                    { fst: actual_pair.0, snd: actual_pair.1 }
                };
            let sp12: &mut [u8] = sp1.snd;
            let sp2: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                {
                    let actual_pair: (&mut [u8], &mut [u8]) = sp12.split_at_mut(length);
                    __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                    { fst: actual_pair.0, snd: actual_pair.1 }
                };
            let sp21: &mut [u8] = sp2.fst;
            sp21.copy_from_slice(x2·);
            let res0: usize = res1.wrapping_add(length);
            let res2: usize = res0;
            res2
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
                              option__LowParse_Pulse_Base_with_perm··CBOR_Pulse_Raw_Type_cbor_raw·::Some
                              { v: a.cbor_array_ptr },
                            _ =>
                              option__LowParse_Pulse_Base_with_perm··CBOR_Pulse_Raw_Type_cbor_raw·::None
                        }
                        {
                            option__LowParse_Pulse_Base_with_perm··CBOR_Pulse_Raw_Type_cbor_raw·::Some
                            { ref v }
                            => v,
                            _ => panic!("Incomplete pattern matching")
                        };
                    let mut pres: [usize; 1] = [res1; 1usize];
                    let mut pi: [usize; 1] = [0usize; 1usize];
                    let i: usize = (&pi)[0];
                    let mut cond: bool = i < argument_as_uint64(xh1.snd) as usize;
                    while
                    cond
                    {
                        let i0: usize = (&pi)[0];
                        let off: usize = (&pres)[0];
                        let e: &cbor_raw = &a[i0];
                        let i·: usize = i0.wrapping_add(1usize);
                        let x2·1: cbor_raw = *e;
                        let res0: usize = ser·(x2·1, out, off);
                        let res2: usize = res0;
                        let res3: usize = res2;
                        (&mut pi)[0] = i·;
                        (&mut pres)[0] = res3;
                        let i1: usize = (&pi)[0];
                        cond = i1 < argument_as_uint64(xh1.snd) as usize
                    };
                    let res0: usize = (&pres)[0];
                    let res2: usize = res0;
                    let res3: usize = res2;
                    res3
                }
                else
                {
                    let xs: cbor_serialized =
                        match x·
                        {
                            cbor_raw::CBOR_Case_Serialized_Array { v: v1 } => v1,
                            _ => panic!("Incomplete pattern matching")
                        };
                    let x2·: &mut [u8] = xs.cbor_serialized_payload;
                    let length: usize = x2·.len();
                    let sp1: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                        {
                            let actual_pair: (&mut [u8], &mut [u8]) = out.split_at_mut(res1);
                            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                            { fst: actual_pair.0, snd: actual_pair.1 }
                        };
                    let sp12: &mut [u8] = sp1.snd;
                    let sp2: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                        {
                            let actual_pair: (&mut [u8], &mut [u8]) = sp12.split_at_mut(length);
                            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                            { fst: actual_pair.0, snd: actual_pair.1 }
                        };
                    let sp21: &mut [u8] = sp2.fst;
                    sp21.copy_from_slice(x2·);
                    let res0: usize = res1.wrapping_add(length);
                    let res2: usize = res0;
                    let res3: usize = res2;
                    res3
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
                                  option__LowParse_Pulse_Base_with_perm··CBOR_Pulse_Raw_Type_cbor_map_entry·::Some
                                  { v: a.cbor_map_ptr },
                                _ =>
                                  option__LowParse_Pulse_Base_with_perm··CBOR_Pulse_Raw_Type_cbor_map_entry·::None
                            }
                            {
                                option__LowParse_Pulse_Base_with_perm··CBOR_Pulse_Raw_Type_cbor_map_entry·::Some
                                { ref v }
                                => v,
                                _ => panic!("Incomplete pattern matching")
                            };
                        let mut pres: [usize; 1] = [res1; 1usize];
                        let mut pi: [usize; 1] = [0usize; 1usize];
                        let i: usize = (&pi)[0];
                        let mut cond: bool = i < argument_as_uint64(xh1.snd) as usize;
                        while
                        cond
                        {
                            let i0: usize = (&pi)[0];
                            let off: usize = (&pres)[0];
                            let e: &cbor_map_entry = &a[i0];
                            let i·: usize = i0.wrapping_add(1usize);
                            let x11: &cbor_raw = &e.cbor_map_entry_key;
                            let res0: usize = ser·(*x11, out, off);
                            let res11: usize = res0;
                            let x2: &cbor_raw = &e.cbor_map_entry_value;
                            let res2: usize = ser·(*x2, out, res11);
                            let res20: usize = res2;
                            let res3: usize = res20;
                            (&mut pi)[0] = i·;
                            (&mut pres)[0] = res3;
                            let i1: usize = (&pi)[0];
                            cond = i1 < argument_as_uint64(xh1.snd) as usize
                        };
                        let res0: usize = (&pres)[0];
                        let res2: usize = res0;
                        let res3: usize = res2;
                        res3
                    }
                    else
                    {
                        let xs: cbor_serialized =
                            match x·
                            {
                                cbor_raw::CBOR_Case_Serialized_Map { v: v1 } => v1,
                                _ => panic!("Incomplete pattern matching")
                            };
                        let x2·: &mut [u8] = xs.cbor_serialized_payload;
                        let length: usize = x2·.len();
                        let sp1: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                            {
                                let actual_pair: (&mut [u8], &mut [u8]) = out.split_at_mut(res1);
                                __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                                { fst: actual_pair.0, snd: actual_pair.1 }
                            };
                        let sp12: &mut [u8] = sp1.snd;
                        let sp2: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                            {
                                let actual_pair: (&mut [u8], &mut [u8]) = sp12.split_at_mut(length);
                                __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                                { fst: actual_pair.0, snd: actual_pair.1 }
                            };
                        let sp21: &mut [u8] = sp2.fst;
                        sp21.copy_from_slice(x2·);
                        let res0: usize = res1.wrapping_add(length);
                        let res2: usize = res0;
                        let res3: usize = res2;
                        res3
                    }
                }
                else
                {
                    let b2: initial_byte_t = xh1.fst;
                    if b2.major_type == cbor_major_type_tagged
                    {
                        let res0: usize =
                            if match x· { cbor_raw::CBOR_Case_Tagged { .. } => true, _ => false }
                            {
                                let tg: cbor_tagged =
                                    match x·
                                    {
                                        cbor_raw::CBOR_Case_Tagged { v: v1 } => v1,
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                let x2·: &cbor_raw = &tg.cbor_tagged_ptr[0];
                                let res0: usize = ser·(*x2·, out, res1);
                                let res2: usize = res0;
                                let res3: usize = res2;
                                res3
                            }
                            else
                            {
                                let ser: cbor_serialized =
                                    match x·
                                    {
                                        cbor_raw::CBOR_Case_Serialized_Tagged { v: v1 } => v1,
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                let x2·: &mut [u8] = ser.cbor_serialized_payload;
                                let length: usize = x2·.len();
                                let
                                sp1: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                                =
                                    {
                                        let actual_pair: (&mut [u8], &mut [u8]) =
                                            out.split_at_mut(res1);
                                        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                                        { fst: actual_pair.0, snd: actual_pair.1 }
                                    };
                                let sp12: &mut [u8] = sp1.snd;
                                let
                                sp2: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                                =
                                    {
                                        let actual_pair: (&mut [u8], &mut [u8]) =
                                            sp12.split_at_mut(length);
                                        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                                        { fst: actual_pair.0, snd: actual_pair.1 }
                                    };
                                let sp21: &mut [u8] = sp2.fst;
                                sp21.copy_from_slice(x2·);
                                let res0: usize = res1.wrapping_add(length);
                                let res2: usize = res0;
                                res2
                            };
                        res0
                    }
                    else
                    { res1 }
                }
            }
        };
    let res0: usize = res2;
    let res3: usize = res0;
    res3
}

fn ser <'a>(x1·: cbor_raw <'a>, out: &'a mut [u8], offset: usize) -> usize
{
    let x2·: cbor_raw = x1·;
    let res: usize = ser·(x2·, out, offset);
    let res0: usize = res;
    res0
}

fn cbor_serialize <'a>(x: cbor_raw <'a>, output: &'a mut [u8]) -> usize
{
    let res: usize = ser(x, output, 0usize);
    res
}

pub(crate) fn siz· <'a>(x·: cbor_raw <'a>, out: &'a mut [usize]) -> bool
{
    let res: header = cbor_raw_with_perm_get_header(x·);
    let xh1: header = res;
    let res1: bool = size_header(xh1, out);
    let res0: bool =
        if res1
        {
            let b: initial_byte_t = xh1.fst;
            let res2: bool =
                if
                b.major_type == cbor_major_type_byte_string
                ||
                b.major_type == cbor_major_type_text_string
                {
                    let c·: cbor_string =
                        match x·
                        {
                            cbor_raw::CBOR_Case_String { v: v1 } => v1,
                            _ => panic!("Incomplete pattern matching")
                        };
                    let x2·: &[u8] = c·.cbor_string_ptr;
                    let length: usize = x2·.len();
                    let cur: usize = out[0];
                    let res0: bool =
                        if cur < length
                        { false }
                        else
                        {
                            out[0] = cur.wrapping_sub(length);
                            true
                        };
                    let res2: bool = res0;
                    res2
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
                                      option__LowParse_Pulse_Base_with_perm··CBOR_Pulse_Raw_Type_cbor_raw·::Some
                                      { v: a.cbor_array_ptr },
                                    _ =>
                                      option__LowParse_Pulse_Base_with_perm··CBOR_Pulse_Raw_Type_cbor_raw·::None
                                }
                                {
                                    option__LowParse_Pulse_Base_with_perm··CBOR_Pulse_Raw_Type_cbor_raw·::Some
                                    { ref v }
                                    => v,
                                    _ => panic!("Incomplete pattern matching")
                                };
                            let mut pres: [bool; 1] = [true; 1usize];
                            let mut pi: [usize; 1] = [0usize; 1usize];
                            let res0: bool = (&pres)[0];
                            let i: usize = (&pi)[0];
                            let mut cond: bool = res0 && i < argument_as_uint64(xh1.snd) as usize;
                            while
                            cond
                            {
                                let i0: usize = (&pi)[0];
                                let e: &cbor_raw = &a[i0];
                                let x2·1: cbor_raw = *e;
                                let res2: bool = siz·(x2·1, out);
                                let res3: bool = res2;
                                let res4: bool = res3;
                                if res4
                                {
                                    let i·: usize = i0.wrapping_add(1usize);
                                    (&mut pi)[0] = i·
                                }
                                else
                                { (&mut pres)[0] = false };
                                let res5: bool = (&pres)[0];
                                let i1: usize = (&pi)[0];
                                cond = res5 && i1 < argument_as_uint64(xh1.snd) as usize
                            };
                            let res2: bool = (&pres)[0];
                            let res3: bool = res2;
                            let res4: bool = res3;
                            res4
                        }
                        else
                        {
                            let xs: cbor_serialized =
                                match x·
                                {
                                    cbor_raw::CBOR_Case_Serialized_Array { v: v1 } => v1,
                                    _ => panic!("Incomplete pattern matching")
                                };
                            let x2·: &[u8] = xs.cbor_serialized_payload;
                            let length: usize = x2·.len();
                            let cur: usize = out[0];
                            let res0: bool =
                                if cur < length
                                { false }
                                else
                                {
                                    out[0] = cur.wrapping_sub(length);
                                    true
                                };
                            let res2: bool = res0;
                            let res3: bool = res2;
                            res3
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
                                          option__LowParse_Pulse_Base_with_perm··CBOR_Pulse_Raw_Type_cbor_map_entry·::Some
                                          { v: a.cbor_map_ptr },
                                        _ =>
                                          option__LowParse_Pulse_Base_with_perm··CBOR_Pulse_Raw_Type_cbor_map_entry·::None
                                    }
                                    {
                                        option__LowParse_Pulse_Base_with_perm··CBOR_Pulse_Raw_Type_cbor_map_entry·::Some
                                        { ref v }
                                        => v,
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                let mut pres: [bool; 1] = [true; 1usize];
                                let mut pi: [usize; 1] = [0usize; 1usize];
                                let res0: bool = (&pres)[0];
                                let i: usize = (&pi)[0];
                                let mut cond: bool =
                                    res0 && i < argument_as_uint64(xh1.snd) as usize;
                                while
                                cond
                                {
                                    let i0: usize = (&pi)[0];
                                    let e: &cbor_map_entry = &a[i0];
                                    let x11: &cbor_raw = &e.cbor_map_entry_key;
                                    let res2: bool = siz·(*x11, out);
                                    let res11: bool = res2;
                                    let res3: bool =
                                        if res11
                                        {
                                            let x2: &cbor_raw = &e.cbor_map_entry_value;
                                            let res3: bool = siz·(*x2, out);
                                            let res20: bool = res3;
                                            res20
                                        }
                                        else
                                        { false };
                                    if res3
                                    {
                                        let i·: usize = i0.wrapping_add(1usize);
                                        (&mut pi)[0] = i·
                                    }
                                    else
                                    { (&mut pres)[0] = false };
                                    let res4: bool = (&pres)[0];
                                    let i1: usize = (&pi)[0];
                                    cond = res4 && i1 < argument_as_uint64(xh1.snd) as usize
                                };
                                let res2: bool = (&pres)[0];
                                let res3: bool = res2;
                                let res4: bool = res3;
                                res4
                            }
                            else
                            {
                                let xs: cbor_serialized =
                                    match x·
                                    {
                                        cbor_raw::CBOR_Case_Serialized_Map { v: v1 } => v1,
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                let x2·: &[u8] = xs.cbor_serialized_payload;
                                let length: usize = x2·.len();
                                let cur: usize = out[0];
                                let res0: bool =
                                    if cur < length
                                    { false }
                                    else
                                    {
                                        out[0] = cur.wrapping_sub(length);
                                        true
                                    };
                                let res2: bool = res0;
                                let res3: bool = res2;
                                res3
                            }
                        }
                        else
                        {
                            let b2: initial_byte_t = xh1.fst;
                            if b2.major_type == cbor_major_type_tagged
                            {
                                let res0: bool =
                                    if
                                    match x·
                                    { cbor_raw::CBOR_Case_Tagged { .. } => true, _ => false }
                                    {
                                        let tg: cbor_tagged =
                                            match x·
                                            {
                                                cbor_raw::CBOR_Case_Tagged { v: v1 } => v1,
                                                _ => panic!("Incomplete pattern matching")
                                            };
                                        let x2·: &cbor_raw = &tg.cbor_tagged_ptr[0];
                                        let res0: bool = siz·(*x2·, out);
                                        let res2: bool = res0;
                                        let res3: bool = res2;
                                        res3
                                    }
                                    else
                                    {
                                        let ser1: cbor_serialized =
                                            match x·
                                            {
                                                cbor_raw::CBOR_Case_Serialized_Tagged { v: v1 } =>
                                                  v1,
                                                _ => panic!("Incomplete pattern matching")
                                            };
                                        let x2·: &[u8] = ser1.cbor_serialized_payload;
                                        let length: usize = x2·.len();
                                        let cur: usize = out[0];
                                        let res0: bool =
                                            if cur < length
                                            { false }
                                            else
                                            {
                                                out[0] = cur.wrapping_sub(length);
                                                true
                                            };
                                        let res2: bool = res0;
                                        res2
                                    };
                                res0
                            }
                            else
                            { true }
                        }
                    }
                };
            res2
        }
        else
        { false };
    let res2: bool = res0;
    res2
}

fn siz <'a>(x1·: cbor_raw <'a>, out: &'a mut [usize]) -> bool
{
    let x2·: cbor_raw = x1·;
    let res: bool = siz·(x2·, out);
    let res0: bool = res;
    res0
}

fn cbor_size <'a>(x: cbor_raw <'a>, bound: usize) -> usize
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

fn read_initial_byte_t(input: &[u8]) -> initial_byte_t
{
    let last: u8 = input[0usize];
    let res: u8 = last;
    let x: u8 = res;
    let res0: initial_byte_t =
        initial_byte_t
        {
            major_type: get_bitfield_gen8(x, 5u32, 8u32),
            additional_info: get_bitfield_gen8(x, 0u32, 5u32)
        };
    let res1: initial_byte_t = res0;
    let res2: initial_byte_t = res1;
    let res3: initial_byte_t = res2;
    res3
}

fn read_header(input: &mut [u8]) -> header
{
    let i: usize = 1usize;
    let s: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        {
            let actual_pair: (&mut [u8], &mut [u8]) = input.split_at_mut(i);
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
            { fst: actual_pair.0, snd: actual_pair.1 }
        };
    let s1: &mut [u8] = s.fst;
    let s2: &mut [u8] = s.snd;
    let res: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s1, snd: s2 };
    let input1: &mut [u8] = res.fst;
    let input2: &mut [u8] = res.snd;
    let split12: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: input1, snd: input2 };
    let input10: &[u8] = split12.fst;
    let input20: &[u8] = split12.snd;
    let x: initial_byte_t = read_initial_byte_t(input10);
    let res0: initial_byte_t = x;
    let x1: initial_byte_t = res0;
    let x2: long_argument =
        if x1.additional_info == additional_info_long_argument_8_bits
        {
            if x1.major_type == cbor_major_type_simple_value
            {
                let last: u8 = input20[0usize];
                let res1: u8 = last;
                let x0: u8 = res1;
                let res2: long_argument = long_argument::LongArgumentSimpleValue { v: x0 };
                let res3: long_argument = res2;
                let res4: long_argument = res3;
                res4
            }
            else
            {
                let last: u8 = input20[0usize];
                let res1: u8 = last;
                let x0: u8 = res1;
                let res2: long_argument = long_argument::LongArgumentU8 { v: x0 };
                let res3: long_argument = res2;
                res3
            }
        }
        else if x1.additional_info == additional_info_long_argument_16_bits
        {
            let pos·: usize = 1usize;
            let last: u8 = input20[pos·];
            let last1: u8 = input20[0usize];
            let n: u16 = last1 as u16;
            let blast: u16 = last as u16;
            let res1: u16 = blast.wrapping_add(n.wrapping_mul(256u16));
            let x0: u16 = res1;
            let res2: long_argument = long_argument::LongArgumentU16 { v: x0 };
            let res3: long_argument = res2;
            res3
        }
        else if x1.additional_info == additional_info_long_argument_32_bits
        {
            let pos·: usize = 3usize;
            let last: u8 = input20[pos·];
            let pos·1: usize = pos·.wrapping_sub(1usize);
            let last1: u8 = input20[pos·1];
            let pos·2: usize = pos·1.wrapping_sub(1usize);
            let last2: u8 = input20[pos·2];
            let last3: u8 = input20[0usize];
            let n: u32 = last3 as u32;
            let blast: u32 = last2 as u32;
            let n0: u32 = blast.wrapping_add(n.wrapping_mul(256u32));
            let blast0: u32 = last1 as u32;
            let n1: u32 = blast0.wrapping_add(n0.wrapping_mul(256u32));
            let blast1: u32 = last as u32;
            let res1: u32 = blast1.wrapping_add(n1.wrapping_mul(256u32));
            let x0: u32 = res1;
            let res2: long_argument = long_argument::LongArgumentU32 { v: x0 };
            let res3: long_argument = res2;
            res3
        }
        else if x1.additional_info == additional_info_long_argument_64_bits
        {
            let pos·: usize = 7usize;
            let last: u8 = input20[pos·];
            let pos·1: usize = pos·.wrapping_sub(1usize);
            let last1: u8 = input20[pos·1];
            let pos·2: usize = pos·1.wrapping_sub(1usize);
            let last2: u8 = input20[pos·2];
            let pos·3: usize = pos·2.wrapping_sub(1usize);
            let last3: u8 = input20[pos·3];
            let pos·4: usize = pos·3.wrapping_sub(1usize);
            let last4: u8 = input20[pos·4];
            let pos·5: usize = pos·4.wrapping_sub(1usize);
            let last5: u8 = input20[pos·5];
            let pos·6: usize = pos·5.wrapping_sub(1usize);
            let last6: u8 = input20[pos·6];
            let last7: u8 = input20[0usize];
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
            let res1: u64 = blast5.wrapping_add(n5.wrapping_mul(256u64));
            let x0: u64 = res1;
            let res2: long_argument = long_argument::LongArgumentU64 { v: x0 };
            let res3: long_argument = res2;
            res3
        }
        else
        { long_argument::LongArgumentOther { a: x1.additional_info } };
    let res1: header = header { fst: x1, snd: x2 };
    res1
}

fn validate_header(input: &mut [u8], poffset: &mut [usize]) -> bool
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
            let s·: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                {
                    let actual_pair: (&mut [u8], &mut [u8]) = input.split_at_mut(offset2);
                    __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                    { fst: actual_pair.0, snd: actual_pair.1 }
                };
            let s1: &mut [u8] = s·.fst;
            let s2: &mut [u8] = s·.snd;
            let split123: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s1, snd: s2 };
            let input23: &mut [u8] = split123.snd;
            let consumed: usize = off.wrapping_sub(offset2);
            let s1s2: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                {
                    let actual_pair: (&mut [u8], &mut [u8]) = input23.split_at_mut(consumed);
                    __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                    { fst: actual_pair.0, snd: actual_pair.1 }
                };
            let s10: &mut [u8] = s1s2.fst;
            let s20: &mut [u8] = s1s2.snd;
            let res: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                { fst: s10, snd: s20 };
            let left: &mut [u8] = res.fst;
            let right: &mut [u8] = res.snd;
            let split23: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                { fst: left, snd: right };
            let input·: &[u8] = split23.fst;
            let res0: initial_byte_t = read_initial_byte_t(input·);
            let x: initial_byte_t = res0;
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
        let s·: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
            {
                let actual_pair: (&mut [u8], &mut [u8]) = input.split_at_mut(offset1);
                __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                { fst: actual_pair.0, snd: actual_pair.1 }
            };
        let s1: &mut [u8] = s·.fst;
        let s2: &mut [u8] = s·.snd;
        let split123: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s1, snd: s2 };
        let input23: &mut [u8] = split123.snd;
        let consumed: usize = off.wrapping_sub(offset1);
        let s1s2: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
            {
                let actual_pair: (&mut [u8], &mut [u8]) = input23.split_at_mut(consumed);
                __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                { fst: actual_pair.0, snd: actual_pair.1 }
            };
        let s10: &mut [u8] = s1s2.fst;
        let s20: &mut [u8] = s1s2.snd;
        let res: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s10, snd: s20 };
        let left: &mut [u8] = res.fst;
        let right: &mut [u8] = res.snd;
        let split23: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
            { fst: left, snd: right };
        let input·: &[u8] = split23.fst;
        let x: initial_byte_t = read_initial_byte_t(input·);
        let res0: initial_byte_t = x;
        let res1: initial_byte_t = res0;
        let x0: initial_byte_t = res1;
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
                    let s·0: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                        {
                            let actual_pair: (&mut [u8], &mut [u8]) = input.split_at_mut(offset20);
                            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                            { fst: actual_pair.0, snd: actual_pair.1 }
                        };
                    let s11: &mut [u8] = s·0.fst;
                    let s21: &mut [u8] = s·0.snd;
                    let split1230: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                        { fst: s11, snd: s21 };
                    let input230: &mut [u8] = split1230.snd;
                    let consumed0: usize = off1.wrapping_sub(offset20);
                    let s1s20: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                        {
                            let actual_pair: (&mut [u8], &mut [u8]) =
                                input230.split_at_mut(consumed0);
                            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                            { fst: actual_pair.0, snd: actual_pair.1 }
                        };
                    let s12: &mut [u8] = s1s20.fst;
                    let s22: &mut [u8] = s1s20.snd;
                    let res2: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                        { fst: s12, snd: s22 };
                    let left0: &mut [u8] = res2.fst;
                    let right0: &mut [u8] = res2.snd;
                    let split230: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                        { fst: left0, snd: right0 };
                    let input·0: &[u8] = split230.fst;
                    let last: u8 = input·0[0usize];
                    let res3: u8 = last;
                    let res4: u8 = res3;
                    let x1: u8 = res4;
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

fn jump_header(input: &mut [u8], offset: usize) -> usize
{
    let off1: usize = offset.wrapping_add(1usize);
    let s·: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        {
            let actual_pair: (&mut [u8], &mut [u8]) = input.split_at_mut(offset);
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
            { fst: actual_pair.0, snd: actual_pair.1 }
        };
    let s1: &mut [u8] = s·.fst;
    let s2: &mut [u8] = s·.snd;
    let split123: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s1, snd: s2 };
    let input23: &mut [u8] = split123.snd;
    let consumed: usize = off1.wrapping_sub(offset);
    let s1s2: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        {
            let actual_pair: (&mut [u8], &mut [u8]) = input23.split_at_mut(consumed);
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
            { fst: actual_pair.0, snd: actual_pair.1 }
        };
    let s10: &mut [u8] = s1s2.fst;
    let s20: &mut [u8] = s1s2.snd;
    let res: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s10, snd: s20 };
    let left: &mut [u8] = res.fst;
    let right: &mut [u8] = res.snd;
    let split23: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: left, snd: right };
    let input·: &[u8] = split23.fst;
    let x: initial_byte_t = read_initial_byte_t(input·);
    let res0: initial_byte_t = x;
    let res1: initial_byte_t = res0;
    let x0: initial_byte_t = res1;
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

fn validate_recursive_step_count_leaf(a: &mut [u8], bound: usize, prem: &mut [usize]) -> bool
{
    let i: usize = jump_header(a, 0usize);
    let s: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        {
            let actual_pair: (&mut [u8], &mut [u8]) = a.split_at_mut(i);
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
            { fst: actual_pair.0, snd: actual_pair.1 }
        };
    let s1: &mut [u8] = s.fst;
    let s2: &mut [u8] = s.snd;
    let res: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s1, snd: s2 };
    let input1: &mut [u8] = res.fst;
    let input2: &mut [u8] = res.snd;
    let spl: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: input1, snd: input2 };
    let input10: &mut [u8] = spl.fst;
    let h: header = read_header(input10);
    let typ: u8 = get_header_major_type(h);
    if typ == cbor_major_type_array
    {
        let l: long_argument = h.snd;
        let arg64: u64 = argument_as_uint64(l);
        prem[0] = arg64 as usize;
        false
    }
    else if typ == cbor_major_type_map
    {
        let l: long_argument = h.snd;
        let arg64: u64 = argument_as_uint64(l);
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

fn jump_recursive_step_count_leaf(a: &mut [u8]) -> usize
{
    let i: usize = jump_header(a, 0usize);
    let s: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        {
            let actual_pair: (&mut [u8], &mut [u8]) = a.split_at_mut(i);
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
            { fst: actual_pair.0, snd: actual_pair.1 }
        };
    let s1: &mut [u8] = s.fst;
    let s2: &mut [u8] = s.snd;
    let res: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s1, snd: s2 };
    let input1: &mut [u8] = res.fst;
    let input2: &mut [u8] = res.snd;
    let spl: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: input1, snd: input2 };
    let input10: &mut [u8] = spl.fst;
    let h: header = read_header(input10);
    let typ: u8 = get_header_major_type(h);
    if typ == cbor_major_type_array
    {
        let l: long_argument = h.snd;
        let arg64: u64 = argument_as_uint64(l);
        arg64 as usize
    }
    else if typ == cbor_major_type_map
    {
        let l: long_argument = h.snd;
        let arg64: u64 = argument_as_uint64(l);
        let arg: usize = arg64 as usize;
        arg.wrapping_add(arg)
    }
    else if typ == cbor_major_type_tagged { 1usize } else { 0usize }
}

fn validate_raw_data_item(input: &mut [u8], poffset: &mut [usize]) -> bool
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
                    let s·: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                        {
                            let actual_pair: (&mut [u8], &mut [u8]) = input.split_at_mut(offset1);
                            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                            { fst: actual_pair.0, snd: actual_pair.1 }
                        };
                    let s1: &mut [u8] = s·.fst;
                    let s2: &mut [u8] = s·.snd;
                    let split123: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                        { fst: s1, snd: s2 };
                    let input23: &mut [u8] = split123.snd;
                    let consumed: usize = off1.wrapping_sub(offset1);
                    let s1s2: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                        {
                            let actual_pair: (&mut [u8], &mut [u8]) =
                                input23.split_at_mut(consumed);
                            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                            { fst: actual_pair.0, snd: actual_pair.1 }
                        };
                    let s10: &mut [u8] = s1s2.fst;
                    let s20: &mut [u8] = s1s2.snd;
                    let res0: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                        { fst: s10, snd: s20 };
                    let left: &mut [u8] = res0.fst;
                    let right: &mut [u8] = res0.snd;
                    let split23: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                        { fst: left, snd: right };
                    let input·: &mut [u8] = split23.fst;
                    let res1: header = read_header(input·);
                    let x: header = res1;
                    let b: initial_byte_t = x.fst;
                    if
                    b.major_type == cbor_major_type_byte_string
                    ||
                    b.major_type == cbor_major_type_text_string
                    {
                        let offset2: usize = poffset[0];
                        let l: long_argument = x.snd;
                        if input.len().wrapping_sub(offset2) < argument_as_uint64(l) as usize
                        { false }
                        else
                        {
                            let l0: long_argument = x.snd;
                            poffset[0] = offset2.wrapping_add(argument_as_uint64(l0) as usize);
                            true
                        }
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
                let s·: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    {
                        let actual_pair: (&mut [u8], &mut [u8]) = input.split_at_mut(off);
                        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                        { fst: actual_pair.0, snd: actual_pair.1 }
                    };
                let s1: &mut [u8] = s·.fst;
                let s2: &mut [u8] = s·.snd;
                let split123: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                    { fst: s1, snd: s2 };
                let input23: &mut [u8] = split123.snd;
                let consumed: usize = offset10.wrapping_sub(off);
                let s1s2: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    {
                        let actual_pair: (&mut [u8], &mut [u8]) = input23.split_at_mut(consumed);
                        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                        { fst: actual_pair.0, snd: actual_pair.1 }
                    };
                let s10: &mut [u8] = s1s2.fst;
                let s20: &mut [u8] = s1s2.snd;
                let res0: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                    { fst: s10, snd: s20 };
                let left: &mut [u8] = res0.fst;
                let right: &mut [u8] = res0.snd;
                let split23: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                    { fst: left, snd: right };
                let input1: &mut [u8] = split23.fst;
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

fn jump_raw_data_item(input: &mut [u8], offset: usize) -> usize
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
        let s·: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
            {
                let actual_pair: (&mut [u8], &mut [u8]) = input.split_at_mut(off);
                __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                { fst: actual_pair.0, snd: actual_pair.1 }
            };
        let s1: &mut [u8] = s·.fst;
        let s2: &mut [u8] = s·.snd;
        let split123: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s1, snd: s2 };
        let input23: &mut [u8] = split123.snd;
        let consumed: usize = off1.wrapping_sub(off);
        let s1s2: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
            {
                let actual_pair: (&mut [u8], &mut [u8]) = input23.split_at_mut(consumed);
                __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                { fst: actual_pair.0, snd: actual_pair.1 }
            };
        let s10: &mut [u8] = s1s2.fst;
        let s20: &mut [u8] = s1s2.snd;
        let res: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s10, snd: s20 };
        let left: &mut [u8] = res.fst;
        let right: &mut [u8] = res.snd;
        let split23: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
            { fst: left, snd: right };
        let input·: &mut [u8] = split23.fst;
        let res0: header = read_header(input·);
        let x: header = res0;
        let b: initial_byte_t = x.fst;
        let off10: usize =
            if
            b.major_type == cbor_major_type_byte_string
            ||
            b.major_type == cbor_major_type_text_string
            {
                let l: long_argument = x.snd;
                off1.wrapping_add(argument_as_uint64(l) as usize)
            }
            else
            { off1.wrapping_add(0usize) };
        (&mut poffset)[0] = off10;
        let s·0: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
            {
                let actual_pair: (&mut [u8], &mut [u8]) = input.split_at_mut(off);
                __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                { fst: actual_pair.0, snd: actual_pair.1 }
            };
        let s11: &mut [u8] = s·0.fst;
        let s21: &mut [u8] = s·0.snd;
        let split1230: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s11, snd: s21 };
        let input230: &mut [u8] = split1230.snd;
        let consumed0: usize = off10.wrapping_sub(off);
        let s1s20: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
            {
                let actual_pair: (&mut [u8], &mut [u8]) = input230.split_at_mut(consumed0);
                __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                { fst: actual_pair.0, snd: actual_pair.1 }
            };
        let s12: &mut [u8] = s1s20.fst;
        let s22: &mut [u8] = s1s20.snd;
        let res1: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s12, snd: s22 };
        let left0: &mut [u8] = res1.fst;
        let right0: &mut [u8] = res1.snd;
        let split230: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
            { fst: left0, snd: right0 };
        let input1: &mut [u8] = split230.fst;
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

fn cbor_read <'a>(input: &'a mut [u8]) -> cbor_raw <'a>
{
    let mut ph: [header; 1] =
        [header
            {
                fst:
                initial_byte_t { major_type: cbor_major_type_simple_value, additional_info: 0u8 },
                snd:
                long_argument::LongArgumentOther
                {
                    a:
                    initial_byte_t
                    { major_type: cbor_major_type_simple_value, additional_info: 0u8 }.additional_info
                }
            };
            1usize];
    let i: usize = jump_header(input, 0usize);
    let s: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        {
            let actual_pair: (&mut [u8], &mut [u8]) = input.split_at_mut(i);
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
            { fst: actual_pair.0, snd: actual_pair.1 }
        };
    let s1: &mut [u8] = s.fst;
    let s2: &mut [u8] = s.snd;
    let res: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s1, snd: s2 };
    let input1: &mut [u8] = res.fst;
    let input2: &mut [u8] = res.snd;
    let spl: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: input1, snd: input2 };
    let ph1: &mut [u8] = spl.fst;
    let outc: &mut [u8] = spl.snd;
    let h: header = read_header(ph1);
    (&mut ph)[0] = h;
    let pc: &mut [u8] = outc;
    let h0: header = (&ph)[0];
    let typ: u8 = h0.fst.major_type;
    if typ == cbor_major_type_uint64 || typ == cbor_major_type_neg_int64
    {
        let l: long_argument = h0.snd;
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
                long_argument::LongArgumentOther { a: v1 } =>
                  raw_uint64 { size: 0u8, value: v1 as u64 },
                _ => panic!("Incomplete pattern matching")
            };
        let resi: cbor_int =
            cbor_int { cbor_int_type: typ, cbor_int_size: i0.size, cbor_int_value: i0.value };
        cbor_raw::CBOR_Case_Int { v: resi }
    }
    else if typ == cbor_major_type_text_string || typ == cbor_major_type_byte_string
    {
        let l: long_argument = h0.snd;
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
                long_argument::LongArgumentOther { a: v1 } =>
                  raw_uint64 { size: 0u8, value: v1 as u64 },
                _ => panic!("Incomplete pattern matching")
            };
        let ress: cbor_string =
            cbor_string { cbor_string_type: typ, cbor_string_size: i0.size, cbor_string_ptr: pc };
        cbor_raw::CBOR_Case_String { v: ress }
    }
    else if typ == cbor_major_type_tagged
    {
        let l: long_argument = h0.snd;
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
                long_argument::LongArgumentOther { a: v1 } =>
                  raw_uint64 { size: 0u8, value: v1 as u64 },
                _ => panic!("Incomplete pattern matching")
            };
        let rest: cbor_serialized =
            cbor_serialized { cbor_serialized_header: tag, cbor_serialized_payload: pc };
        cbor_raw::CBOR_Case_Serialized_Tagged { v: rest }
    }
    else if typ == cbor_major_type_array
    {
        let l: long_argument = h0.snd;
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
                long_argument::LongArgumentOther { a: v1 } =>
                  raw_uint64 { size: 0u8, value: v1 as u64 },
                _ => panic!("Incomplete pattern matching")
            };
        let resa: cbor_serialized =
            cbor_serialized { cbor_serialized_header: len, cbor_serialized_payload: pc };
        cbor_raw::CBOR_Case_Serialized_Array { v: resa }
    }
    else if typ == cbor_major_type_map
    {
        let l: long_argument = h0.snd;
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
                long_argument::LongArgumentOther { a: v1 } =>
                  raw_uint64 { size: 0u8, value: v1 as u64 },
                _ => panic!("Incomplete pattern matching")
            };
        let resa: cbor_serialized =
            cbor_serialized { cbor_serialized_header: len, cbor_serialized_payload: pc };
        cbor_raw::CBOR_Case_Serialized_Map { v: resa }
    }
    else
    {
        let l: long_argument = h0.snd;
        let i0: u8 =
            match l
            {
                long_argument::LongArgumentOther { a: v1 } => v1,
                long_argument::LongArgumentSimpleValue { v: v1 } => v1,
                _ => panic!("Incomplete pattern matching")
            };
        cbor_raw::CBOR_Case_Simple { v: i0 }
    }
}

fn cbor_match_serialized_tagged_get_payload <'a>(c: cbor_serialized <'a>) -> cbor_raw <'a>
{
    let res: cbor_raw = cbor_read(c.cbor_serialized_payload);
    res
}

fn cbor_serialized_array_iterator_init <'a>(c: cbor_serialized <'a>) -> &'a [u8]
{ c.cbor_serialized_payload }

fn cbor_serialized_array_iterator_is_empty(c: &[u8]) -> bool { c.len() == 0usize }

#[derive(PartialEq, Clone, Copy)]
enum cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_tags
{
    CBOR_Raw_Iterator_Slice,
    CBOR_Raw_Iterator_Serialized
}

#[derive(PartialEq)]
pub enum cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>
{
    CBOR_Raw_Iterator_Slice { _0: &'a [cbor_raw <'a>] },
    CBOR_Raw_Iterator_Serialized { _0: &'a mut [u8] }
}

fn cbor_serialized_array_iterator_next <'a>(
    pi: &'a mut [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>],
    i: &'a mut [u8]
) ->
    cbor_raw
    <'a>
{
    let i1: usize = jump_raw_data_item(i, 0usize);
    let s: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        {
            let actual_pair: (&mut [u8], &mut [u8]) = i.split_at_mut(i1);
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
            { fst: actual_pair.0, snd: actual_pair.1 }
        };
    let s1: &mut [u8] = s.fst;
    let s2: &mut [u8] = s.snd;
    let res: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s1, snd: s2 };
    let input1: &mut [u8] = res.fst;
    let input2: &mut [u8] = res.snd;
    let res0: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: input1, snd: input2 };
    let input10: &mut [u8] = res0.fst;
    let input20: &mut [u8] = res0.snd;
    let sp: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
        { fst: input10, snd: input20 };
    let s10: &mut [u8] = sp.fst;
    let s20: &[u8] = sp.snd;
    let res1: cbor_raw = cbor_read(s10);
    let i·: &[u8] = s20;
    pi[0] =
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized { _0: i· };
    res1
}

fn cbor_serialized_map_iterator_init <'a>(c: cbor_serialized <'a>) -> &'a [u8]
{ c.cbor_serialized_payload }

fn cbor_serialized_map_iterator_is_empty(c: &[u8]) -> bool { c.len() == 0usize }

#[derive(PartialEq)]
pub enum cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>
{
    CBOR_Raw_Iterator_Slice { _0: &'a [cbor_map_entry <'a>] },
    CBOR_Raw_Iterator_Serialized { _0: &'a mut [u8] }
}

fn cbor_serialized_map_iterator_next <'a>(
    pi: &'a mut [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>],
    i: &'a mut [u8]
) ->
    cbor_map_entry
    <'a>
{
    let off1: usize = jump_raw_data_item(i, 0usize);
    let i1: usize = jump_raw_data_item(i, off1);
    let s: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        {
            let actual_pair: (&mut [u8], &mut [u8]) = i.split_at_mut(i1);
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
            { fst: actual_pair.0, snd: actual_pair.1 }
        };
    let s1: &mut [u8] = s.fst;
    let s2: &mut [u8] = s.snd;
    let res: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s1, snd: s2 };
    let input1: &mut [u8] = res.fst;
    let input2: &mut [u8] = res.snd;
    let res0: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: input1, snd: input2 };
    let input10: &mut [u8] = res0.fst;
    let input20: &mut [u8] = res0.snd;
    let sp: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
        { fst: input10, snd: input20 };
    let s10: &mut [u8] = sp.fst;
    let s20: &[u8] = sp.snd;
    let i10: usize = jump_raw_data_item(s10, 0usize);
    let s0: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        {
            let actual_pair: (&mut [u8], &mut [u8]) = s10.split_at_mut(i10);
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
            { fst: actual_pair.0, snd: actual_pair.1 }
        };
    let s11: &mut [u8] = s0.fst;
    let s21: &mut [u8] = s0.snd;
    let res1: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s11, snd: s21 };
    let input11: &mut [u8] = res1.fst;
    let input21: &mut [u8] = res1.snd;
    let res2: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
        { fst: input11, snd: input21 };
    let input12: &mut [u8] = res2.fst;
    let input22: &mut [u8] = res2.snd;
    let sp1: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
        { fst: input12, snd: input22 };
    let s110: &mut [u8] = sp1.fst;
    let s210: &mut [u8] = sp1.snd;
    let res10: cbor_raw = cbor_read(s110);
    let res20: cbor_raw = cbor_read(s210);
    let res3: cbor_map_entry =
        cbor_map_entry { cbor_map_entry_key: res10, cbor_map_entry_value: res20 };
    let i·: &[u8] = s20;
    pi[0] =
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
        { _0: i· };
    res3
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
        let res0: i16 = impl_uint8_compare(x1, x2);
        let c: i16 = res0;
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
        let res1: i16 = (&pres)[0];
        let i11: usize = (&pi1)[0];
        cond = res1 == 0i16 && i11 < n1
    };
    let res0: i16 = (&pres)[0];
    let res1: i16 = res0;
    res1
}

fn cbor_match_tagged_get_payload <'a>(c: cbor_raw <'a>) -> cbor_raw <'a>
{
    if match c { cbor_raw::CBOR_Case_Serialized_Tagged { .. } => true, _ => false }
    {
        let cs: cbor_serialized =
            match c
            {
                cbor_raw::CBOR_Case_Serialized_Tagged { v } => v,
                _ => panic!("Incomplete pattern matching")
            };
        let res: cbor_raw = cbor_match_serialized_tagged_get_payload(cs);
        res
    }
    else
    {
        let ct: cbor_tagged =
            match c
            { cbor_raw::CBOR_Case_Tagged { v } => v, _ => panic!("Incomplete pattern matching") };
        ct.cbor_tagged_ptr[0]
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
              let i·: &[u8] = cbor_serialized_array_iterator_init(c·);
              cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized
              { _0: i· }
          },
        cbor_raw::CBOR_Case_Array { v: c· } =>
          {
              let s: &[cbor_raw] = c·.cbor_array_ptr;
              let s0: &[cbor_raw] = s;
              let i: &[cbor_raw] = s0;
              let res: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice { _0: i };
              res
          },
        _ => panic!("Incomplete pattern matching")
    }
}

fn cbor_array_iterator_is_empty <'a>(c: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>) ->
    bool
{
    match c
    {
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice { _0: ref c· } =>
          {
              let res: bool = c·.len() == 0usize;
              let res0: bool = res;
              res0
          },
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized
        { _0: ref c· }
        =>
          {
              let res: bool = cbor_serialized_array_iterator_is_empty(c·);
              res
          },
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq)]
struct
__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw
<'a>
{ pub fst: &'a [cbor_raw <'a>], pub snd: &'a [cbor_raw <'a>] }

fn cbor_array_iterator_next <'a>(
    mut pi: &'a mut [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>]
) ->
    cbor_raw
    <'a>
{
    let i0: &mut cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = &mut pi[0];
    match *i0
    {
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice { _0: ref i1 } =>
          {
              let res: &cbor_raw = &i1[0usize];
              let
              sp:
              __Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw
              =
                  {
                      let actual_pair: (&[cbor_raw], &[cbor_raw]) = i1.split_at(1usize);
                      __Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw
                      { fst: actual_pair.0, snd: actual_pair.1 }
                  };
              let s·: &[cbor_raw] = sp.snd;
              let i11: &[cbor_raw] = s·;
              let i·: &[cbor_raw] = i11;
              pi[0] =
                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice
                  { _0: i· };
              let res0: cbor_raw = *res;
              res0
          },
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized
        { _0: ref mut i1 }
        =>
          {
              let res: cbor_raw = cbor_serialized_array_iterator_next(pi, i1);
              res
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
              let i·: &[u8] = cbor_serialized_map_iterator_init(c·);
              cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
              { _0: i· }
          },
        cbor_raw::CBOR_Case_Map { v: c· } =>
          {
              let s: &[cbor_map_entry] = c·.cbor_map_ptr;
              let s0: &[cbor_map_entry] = s;
              let i: &[cbor_map_entry] = s0;
              let res: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
                  { _0: i };
              res
          },
        _ => panic!("Incomplete pattern matching")
    }
}

fn cbor_map_iterator_is_empty <'a>(
    c: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>
) ->
    bool
{
    match c
    {
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
        { _0: ref c· }
        =>
          {
              let res: bool = c·.len() == 0usize;
              let res0: bool = res;
              res0
          },
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
        { _0: ref c· }
        =>
          {
              let res: bool = cbor_serialized_map_iterator_is_empty(c·);
              res
          },
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq)]
struct
__Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry
<'a>
{ pub fst: &'a [cbor_map_entry <'a>], pub snd: &'a [cbor_map_entry <'a>] }

fn cbor_map_iterator_next <'a>(
    mut pi: &'a mut [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>]
) ->
    cbor_map_entry
    <'a>
{
    let i0: &mut cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry = &mut pi[0];
    match *i0
    {
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
        { _0: ref i1 }
        =>
          {
              let res: &cbor_map_entry = &i1[0usize];
              let
              sp:
              __Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry
              =
                  {
                      let actual_pair: (&[cbor_map_entry], &[cbor_map_entry]) = i1.split_at(1usize);
                      __Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry
                      { fst: actual_pair.0, snd: actual_pair.1 }
                  };
              let s·: &[cbor_map_entry] = sp.snd;
              let i11: &[cbor_map_entry] = s·;
              let i·: &[cbor_map_entry] = i11;
              pi[0] =
                  cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
                  { _0: i· };
              let res0: cbor_map_entry = *res;
              res0
          },
        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
        { _0: ref mut i1 }
        =>
          {
              let res: cbor_map_entry = cbor_serialized_map_iterator_next(pi, i1);
              res
          },
        _ => panic!("Incomplete pattern matching")
    }
}

fn impl_major_type <'a>(x: cbor_raw <'a>) -> u8
{
    match x
    {
        cbor_raw::CBOR_Case_Simple { .. } => cbor_major_type_simple_value,
        cbor_raw::CBOR_Case_Int { .. } =>
          {
              let c·: cbor_int =
                  match x
                  {
                      cbor_raw::CBOR_Case_Int { v: v1 } => v1,
                      _ => panic!("Incomplete pattern matching")
                  };
              c·.cbor_int_type
          },
        cbor_raw::CBOR_Case_String { .. } =>
          {
              let c·: cbor_string =
                  match x
                  {
                      cbor_raw::CBOR_Case_String { v: v1 } => v1,
                      _ => panic!("Incomplete pattern matching")
                  };
              c·.cbor_string_type
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

pub(crate) fn impl_cbor_compare <'a>(x1: cbor_raw <'a>, x2: cbor_raw <'a>) -> i16
{
    let ty1: u8 = impl_major_type(x1);
    let ty2: u8 = impl_major_type(x2);
    let c: i16 = impl_uint8_compare(ty1, ty2);
    if c == 0i16
    {
        if ty1 == cbor_major_type_uint64 || ty1 == cbor_major_type_neg_int64
        {
            let c·: cbor_int =
                match x1
                { cbor_raw::CBOR_Case_Int { v } => v, _ => panic!("Incomplete pattern matching") };
            let i1: raw_uint64 = raw_uint64 { size: c·.cbor_int_size, value: c·.cbor_int_value };
            let c·0: cbor_int =
                match x2
                { cbor_raw::CBOR_Case_Int { v } => v, _ => panic!("Incomplete pattern matching") };
            let i2: raw_uint64 =
                raw_uint64 { size: c·0.cbor_int_size, value: c·0.cbor_int_value };
            impl_raw_uint64_compare(i1, i2)
        }
        else if ty1 == cbor_major_type_byte_string || ty1 == cbor_major_type_text_string
        {
            let c·: cbor_string =
                match x1
                {
                    cbor_raw::CBOR_Case_String { v } => v,
                    _ => panic!("Incomplete pattern matching")
                };
            let res: raw_uint64 =
                raw_uint64 { size: c·.cbor_string_size, value: c·.cbor_string_ptr.len() as u64 };
            let i1: raw_uint64 = res;
            let c·0: cbor_string =
                match x2
                {
                    cbor_raw::CBOR_Case_String { v } => v,
                    _ => panic!("Incomplete pattern matching")
                };
            let res0: raw_uint64 =
                raw_uint64 { size: c·0.cbor_string_size, value: c·0.cbor_string_ptr.len() as u64 };
            let i2: raw_uint64 = res0;
            let c1: i16 = impl_raw_uint64_compare(i1, i2);
            if c1 == 0i16
            {
                let c·1: cbor_string =
                    match x1
                    {
                        cbor_raw::CBOR_Case_String { v } => v,
                        _ => panic!("Incomplete pattern matching")
                    };
                let pl1: &[u8] = c·1.cbor_string_ptr;
                let c·2: cbor_string =
                    match x2
                    {
                        cbor_raw::CBOR_Case_String { v } => v,
                        _ => panic!("Incomplete pattern matching")
                    };
                let pl2: &[u8] = c·2.cbor_string_ptr;
                let res1: i16 = lex_compare_bytes(pl1, pl2);
                res1
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
                let pl1: cbor_raw = cbor_match_tagged_get_payload(x1);
                let pl2: cbor_raw = cbor_match_tagged_get_payload(x2);
                let res: i16 = impl_cbor_compare(pl1, pl2);
                res
            }
            else
            { c1 }
        }
        else if ty1 == cbor_major_type_array
        {
            let len1: raw_uint64 =
                match x1
                {
                    cbor_raw::CBOR_Case_Array { v: c· } => c·.cbor_array_length,
                    cbor_raw::CBOR_Case_Serialized_Array { v: c· } => c·.cbor_serialized_header,
                    _ => panic!("Incomplete pattern matching")
                };
            let len2: raw_uint64 =
                match x2
                {
                    cbor_raw::CBOR_Case_Array { v: c· } => c·.cbor_array_length,
                    cbor_raw::CBOR_Case_Serialized_Array { v: c· } => c·.cbor_serialized_header,
                    _ => panic!("Incomplete pattern matching")
                };
            let c1: i16 = impl_raw_uint64_compare(len1, len2);
            if c1 == 0i16
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
                        { _0: ref c· }
                        =>
                          {
                              let res: bool = c·.len() == 0usize;
                              let res0: bool = res;
                              res0
                          },
                        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized
                        { _0: ref c· }
                        =>
                          {
                              let res: bool = cbor_serialized_array_iterator_is_empty(c·);
                              res
                          },
                        _ => panic!("Incomplete pattern matching")
                    };
                let fin2: bool =
                    match pl2
                    {
                        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice
                        { _0: ref c· }
                        =>
                          {
                              let res: bool = c·.len() == 0usize;
                              let res0: bool = res;
                              res0
                          },
                        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized
                        { _0: ref c· }
                        =>
                          {
                              let res: bool = cbor_serialized_array_iterator_is_empty(c·);
                              res
                          },
                        _ => panic!("Incomplete pattern matching")
                    };
                let res: i16 =
                    if fin1
                    { if fin2 { 0i16 } else { -1i16 } }
                    else if fin2
                    { 1i16 }
                    else
                    {
                        let mut pi1: [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
                            [pl1; 1usize];
                        let mut pi2: [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
                            [pl2; 1usize];
                        let mut pres: [i16; 1] = [0i16; 1usize];
                        let mut pfin1: [bool; 1] = [false; 1usize];
                        let res: i16 = (&pres)[0];
                        let fin11: bool = (&pfin1)[0];
                        let mut cond: bool = res == 0i16 && ! fin11;
                        while
                        cond
                        {
                            let i0: &mut cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                                &mut (&mut pi1)[0];
                            let elt1: cbor_raw =
                                match *i0
                                {
                                    cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice
                                    { _0: ref i }
                                    =>
                                      {
                                          let res0: &cbor_raw = &i[0usize];
                                          let
                                          sp:
                                          __Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw
                                          =
                                              {
                                                  let actual_pair: (&[cbor_raw], &[cbor_raw]) =
                                                      i.split_at(1usize);
                                                  __Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw
                                                  { fst: actual_pair.0, snd: actual_pair.1 }
                                              };
                                          let s·: &[cbor_raw] = sp.snd;
                                          let i11: &[cbor_raw] = s·;
                                          let i·: &[cbor_raw] = i11;
                                          (&mut pi1)[0] =
                                              cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice
                                              { _0: i· };
                                          let res1: cbor_raw = *res0;
                                          res1
                                      },
                                    cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized
                                    { _0: ref mut i }
                                    =>
                                      {
                                          let res0: cbor_raw =
                                              cbor_serialized_array_iterator_next(&mut pi1, i);
                                          res0
                                      },
                                    _ => panic!("Incomplete pattern matching")
                                };
                            let i00: &mut cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                                &mut (&mut pi2)[0];
                            let elt2: cbor_raw =
                                match *i00
                                {
                                    cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice
                                    { _0: ref i }
                                    =>
                                      {
                                          let res0: &cbor_raw = &i[0usize];
                                          let
                                          sp:
                                          __Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw
                                          =
                                              {
                                                  let actual_pair: (&[cbor_raw], &[cbor_raw]) =
                                                      i.split_at(1usize);
                                                  __Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw_Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_raw
                                                  { fst: actual_pair.0, snd: actual_pair.1 }
                                              };
                                          let s·: &[cbor_raw] = sp.snd;
                                          let i11: &[cbor_raw] = s·;
                                          let i·: &[cbor_raw] = i11;
                                          (&mut pi2)[0] =
                                              cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice
                                              { _0: i· };
                                          let res1: cbor_raw = *res0;
                                          res1
                                      },
                                    cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized
                                    { _0: ref mut i }
                                    =>
                                      {
                                          let res0: cbor_raw =
                                              cbor_serialized_array_iterator_next(&mut pi2, i);
                                          res0
                                      },
                                    _ => panic!("Incomplete pattern matching")
                                };
                            let pelt1: cbor_raw = elt1;
                            let pelt2: cbor_raw = elt2;
                            let res0: i16 = impl_cbor_compare(pelt1, pelt2);
                            let c2: i16 = res0;
                            if c2 == 0i16
                            {
                                let i11: &cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                                    &(&pi1)[0];
                                let fin110: bool =
                                    match *i11
                                    {
                                        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice
                                        { _0: ref c· }
                                        =>
                                          {
                                              let res1: bool = c·.len() == 0usize;
                                              let res2: bool = res1;
                                              res2
                                          },
                                        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized
                                        { _0: ref c· }
                                        =>
                                          {
                                              let res1: bool =
                                                  cbor_serialized_array_iterator_is_empty(c·);
                                              res1
                                          },
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                let i21: &cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                                    &(&pi2)[0];
                                let fin21: bool =
                                    match *i21
                                    {
                                        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Slice
                                        { _0: ref c· }
                                        =>
                                          {
                                              let res1: bool = c·.len() == 0usize;
                                              let res2: bool = res1;
                                              res2
                                          },
                                        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw::CBOR_Raw_Iterator_Serialized
                                        { _0: ref c· }
                                        =>
                                          {
                                              let res1: bool =
                                                  cbor_serialized_array_iterator_is_empty(c·);
                                              res1
                                          },
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
                            let res1: i16 = (&pres)[0];
                            let fin110: bool = (&pfin1)[0];
                            cond = res1 == 0i16 && ! fin110
                        };
                        (&pres)[0]
                    };
                let res0: i16 = res;
                res0
            }
            else
            { c1 }
        }
        else if ty1 == cbor_major_type_map
        {
            let len1: raw_uint64 =
                match x1
                {
                    cbor_raw::CBOR_Case_Map { v: c· } => c·.cbor_map_length,
                    cbor_raw::CBOR_Case_Serialized_Map { v: c· } => c·.cbor_serialized_header,
                    _ => panic!("Incomplete pattern matching")
                };
            let len2: raw_uint64 =
                match x2
                {
                    cbor_raw::CBOR_Case_Map { v: c· } => c·.cbor_map_length,
                    cbor_raw::CBOR_Case_Serialized_Map { v: c· } => c·.cbor_serialized_header,
                    _ => panic!("Incomplete pattern matching")
                };
            let c1: i16 = impl_raw_uint64_compare(len1, len2);
            if c1 == 0i16
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
                        { _0: ref c· }
                        =>
                          {
                              let res: bool = c·.len() == 0usize;
                              let res0: bool = res;
                              res0
                          },
                        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
                        { _0: ref c· }
                        =>
                          {
                              let res: bool = cbor_serialized_map_iterator_is_empty(c·);
                              res
                          },
                        _ => panic!("Incomplete pattern matching")
                    };
                let fin2: bool =
                    match pl2
                    {
                        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
                        { _0: ref c· }
                        =>
                          {
                              let res: bool = c·.len() == 0usize;
                              let res0: bool = res;
                              res0
                          },
                        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
                        { _0: ref c· }
                        =>
                          {
                              let res: bool = cbor_serialized_map_iterator_is_empty(c·);
                              res
                          },
                        _ => panic!("Incomplete pattern matching")
                    };
                let res: i16 =
                    if fin1
                    { if fin2 { 0i16 } else { -1i16 } }
                    else if fin2
                    { 1i16 }
                    else
                    {
                        let mut pi1: [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry; 1] =
                            [pl1; 1usize];
                        let mut pi2: [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry; 1] =
                            [pl2; 1usize];
                        let mut pres: [i16; 1] = [0i16; 1usize];
                        let mut pfin1: [bool; 1] = [false; 1usize];
                        let res: i16 = (&pres)[0];
                        let fin11: bool = (&pfin1)[0];
                        let mut cond: bool = res == 0i16 && ! fin11;
                        while
                        cond
                        {
                            let i0: &mut cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
                                &mut (&mut pi1)[0];
                            let elt1: cbor_map_entry =
                                match *i0
                                {
                                    cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
                                    { _0: ref i }
                                    =>
                                      {
                                          let res0: &cbor_map_entry = &i[0usize];
                                          let
                                          sp:
                                          __Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry
                                          =
                                              {
                                                  let
                                                  actual_pair:
                                                  (&[cbor_map_entry], &[cbor_map_entry])
                                                  =
                                                      i.split_at(1usize);
                                                  __Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry
                                                  { fst: actual_pair.0, snd: actual_pair.1 }
                                              };
                                          let s·: &[cbor_map_entry] = sp.snd;
                                          let i11: &[cbor_map_entry] = s·;
                                          let i·: &[cbor_map_entry] = i11;
                                          (&mut pi1)[0] =
                                              cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
                                              { _0: i· };
                                          let res1: cbor_map_entry = *res0;
                                          res1
                                      },
                                    cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
                                    { _0: ref mut i }
                                    =>
                                      {
                                          let res0: cbor_map_entry =
                                              cbor_serialized_map_iterator_next(&mut pi1, i);
                                          res0
                                      },
                                    _ => panic!("Incomplete pattern matching")
                                };
                            let i00: &mut cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
                                &mut (&mut pi2)[0];
                            let elt2: cbor_map_entry =
                                match *i00
                                {
                                    cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
                                    { _0: ref i }
                                    =>
                                      {
                                          let res0: &cbor_map_entry = &i[0usize];
                                          let
                                          sp:
                                          __Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry
                                          =
                                              {
                                                  let
                                                  actual_pair:
                                                  (&[cbor_map_entry], &[cbor_map_entry])
                                                  =
                                                      i.split_at(1usize);
                                                  __Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry_Pulse_Lib_Slice_slice·CBOR_Pulse_Raw_Type_cbor_map_entry
                                                  { fst: actual_pair.0, snd: actual_pair.1 }
                                              };
                                          let s·: &[cbor_map_entry] = sp.snd;
                                          let i11: &[cbor_map_entry] = s·;
                                          let i·: &[cbor_map_entry] = i11;
                                          (&mut pi2)[0] =
                                              cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
                                              { _0: i· };
                                          let res1: cbor_map_entry = *res0;
                                          res1
                                      },
                                    cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
                                    { _0: ref mut i }
                                    =>
                                      {
                                          let res0: cbor_map_entry =
                                              cbor_serialized_map_iterator_next(&mut pi2, i);
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
                                    let c3: i16 =
                                        impl_cbor_compare(
                                            pelt1.cbor_map_entry_value,
                                            pelt2.cbor_map_entry_value
                                        );
                                    c3
                                }
                                else
                                { c2 };
                            if c20 == 0i16
                            {
                                let i11: &cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
                                    &(&pi1)[0];
                                let fin110: bool =
                                    match *i11
                                    {
                                        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
                                        { _0: ref c· }
                                        =>
                                          {
                                              let res0: bool = c·.len() == 0usize;
                                              let res1: bool = res0;
                                              res1
                                          },
                                        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
                                        { _0: ref c· }
                                        =>
                                          {
                                              let res0: bool =
                                                  cbor_serialized_map_iterator_is_empty(c·);
                                              res0
                                          },
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                let i21: &cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry =
                                    &(&pi2)[0];
                                let fin21: bool =
                                    match *i21
                                    {
                                        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Slice
                                        { _0: ref c· }
                                        =>
                                          {
                                              let res0: bool = c·.len() == 0usize;
                                              let res1: bool = res0;
                                              res1
                                          },
                                        cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry::CBOR_Raw_Iterator_Serialized
                                        { _0: ref c· }
                                        =>
                                          {
                                              let res0: bool =
                                                  cbor_serialized_map_iterator_is_empty(c·);
                                              res0
                                          },
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
            else
            { c1 }
        }
        else
        {
            let val1: u8 =
                match x1
                {
                    cbor_raw::CBOR_Case_Simple { v } => v,
                    _ => panic!("Incomplete pattern matching")
                };
            let val2: u8 =
                match x2
                {
                    cbor_raw::CBOR_Case_Simple { v } => v,
                    _ => panic!("Incomplete pattern matching")
                };
            impl_uint8_compare(val1, val2)
        }
    }
    else
    { c }
}

fn cbor_validate(input: &mut [u8]) -> usize
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

fn cbor_raw_ints_optimal(a: &mut [u8]) -> bool
{
    let i: usize = jump_header(a, 0usize);
    let s: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        {
            let actual_pair: (&mut [u8], &mut [u8]) = a.split_at_mut(i);
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
            { fst: actual_pair.0, snd: actual_pair.1 }
        };
    let s1: &mut [u8] = s.fst;
    let s2: &mut [u8] = s.snd;
    let res: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s1, snd: s2 };
    let input1: &mut [u8] = res.fst;
    let input2: &mut [u8] = res.snd;
    let spl: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: input1, snd: input2 };
    let input10: &mut [u8] = spl.fst;
    let h: header = read_header(input10);
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
                long_argument::LongArgumentOther { a: v } =>
                  raw_uint64 { size: 0u8, value: v as u64 },
                _ => panic!("Incomplete pattern matching")
            }
        )
    }
}

fn impl_deterministically_encoded_cbor_map_key_order(a1: &mut [u8], a2: &mut [u8]) -> bool
{
    let i: usize = jump_raw_data_item(a1, 0usize);
    let s: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        {
            let actual_pair: (&mut [u8], &mut [u8]) = a1.split_at_mut(i);
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
            { fst: actual_pair.0, snd: actual_pair.1 }
        };
    let s1: &mut [u8] = s.fst;
    let s2: &mut [u8] = s.snd;
    let res: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s1, snd: s2 };
    let input1: &mut [u8] = res.fst;
    let input2: &mut [u8] = res.snd;
    let res0: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: input1, snd: input2 };
    let input10: &mut [u8] = res0.fst;
    let input20: &mut [u8] = res0.snd;
    let spl: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
        { fst: input10, snd: input20 };
    let k1: &[u8] = spl.fst;
    let i0: usize = jump_raw_data_item(a2, 0usize);
    let s0: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        {
            let actual_pair: (&mut [u8], &mut [u8]) = a2.split_at_mut(i0);
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
            { fst: actual_pair.0, snd: actual_pair.1 }
        };
    let s10: &mut [u8] = s0.fst;
    let s20: &mut [u8] = s0.snd;
    let res1: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s10, snd: s20 };
    let input11: &mut [u8] = res1.fst;
    let input21: &mut [u8] = res1.snd;
    let res2: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
        { fst: input11, snd: input21 };
    let input12: &mut [u8] = res2.fst;
    let input22: &mut [u8] = res2.snd;
    let spl0: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
        { fst: input12, snd: input22 };
    let k2: &[u8] = spl0.fst;
    let res3: i16 = lex_compare_bytes(k1, k2);
    res3 < 0i16
}

fn cbor_raw_sorted(a: &mut [u8]) -> bool
{
    let i: usize = jump_header(a, 0usize);
    let s: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        {
            let actual_pair: (&mut [u8], &mut [u8]) = a.split_at_mut(i);
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
            { fst: actual_pair.0, snd: actual_pair.1 }
        };
    let s1: &mut [u8] = s.fst;
    let s2: &mut [u8] = s.snd;
    let res: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s1, snd: s2 };
    let input1: &mut [u8] = res.fst;
    let input2: &mut [u8] = res.snd;
    let spl: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: input1, snd: input2 };
    let ah: &mut [u8] = spl.fst;
    let ap: &mut [u8] = spl.snd;
    let h: header = read_header(ah);
    if get_header_major_type(h) == cbor_major_type_map
    {
        let l: long_argument = h.snd;
        let n: u64 = argument_as_uint64(l);
        if n as usize == 0usize
        { true }
        else
        {
            let off1: usize = jump_raw_data_item(ap, 0usize);
            let i0: usize = jump_raw_data_item(ap, off1);
            let s10: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                {
                    let actual_pair: (&mut [u8], &mut [u8]) = ap.split_at_mut(i0);
                    __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                    { fst: actual_pair.0, snd: actual_pair.1 }
                };
            let s11: &mut [u8] = s10.fst;
            let s20: &mut [u8] = s10.snd;
            let res0: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                { fst: s11, snd: s20 };
            let input10: &mut [u8] = res0.fst;
            let input20: &mut [u8] = res0.snd;
            let res1: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                { fst: input10, snd: input20 };
            let input11: &mut [u8] = res1.fst;
            let input21: &mut [u8] = res1.snd;
            let res2: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                { fst: input11, snd: input21 };
            let pl: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t = res2;
            let s12: &mut [u8] = pl.fst;
            let s21: &mut [u8] = pl.snd;
            let mut phd: [&mut [u8]; 1] = [s12; 1usize];
            let mut ptl: [&mut [u8]; 1] = [s21; 1usize];
            let n·: usize = (n as usize).wrapping_sub(1usize);
            let mut pi: [usize; 1] = [n·; 1usize];
            let mut pres: [bool; 1] = [true; 1usize];
            let i1: usize = (&pi)[0];
            let res3: bool = (&pres)[0];
            let mut cond: bool = res3 && i1 > 0usize;
            while
            cond
            {
                let stl: &mut [u8] = (&ptl)[0];
                let off10: usize = jump_raw_data_item(stl, 0usize);
                let i2: usize = jump_raw_data_item(stl, off10);
                let s3: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    {
                        let actual_pair: (&mut [u8], &mut [u8]) = stl.split_at_mut(i2);
                        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                        { fst: actual_pair.0, snd: actual_pair.1 }
                    };
                let s110: &mut [u8] = s3.fst;
                let s210: &mut [u8] = s3.snd;
                let res4: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                    { fst: s110, snd: s210 };
                let input12: &mut [u8] = res4.fst;
                let input22: &mut [u8] = res4.snd;
                let res5: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                    { fst: input12, snd: input22 };
                let input13: &mut [u8] = res5.fst;
                let input23: &mut [u8] = res5.snd;
                let res6: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                    { fst: input13, snd: input23 };
                let pl1: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t = res6;
                let s111: &mut [u8] = pl1.fst;
                let s211: &[u8] = pl1.snd;
                let shd: &mut [u8] = (&phd)[0];
                let res7: bool = impl_deterministically_encoded_cbor_map_key_order(shd, s111);
                if res7
                {
                    (&mut phd)[0] = s111;
                    (&mut ptl)[0] = s211;
                    let i3: usize = (&pi)[0];
                    let i·: usize = i3.wrapping_sub(1usize);
                    (&mut pi)[0] = i·
                }
                else
                { (&mut pres)[0] = false };
                let i3: usize = (&pi)[0];
                let res8: bool = (&pres)[0];
                cond = res8 && i3 > 0usize
            };
            (&pres)[0]
        }
    }
    else
    { true }
}

fn cbor_validate_det·(input: &mut [u8]) -> usize
{
    let len: usize = cbor_validate(input);
    if len == 0usize
    { len }
    else
    {
        let s·: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
            {
                let actual_pair: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
                __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                { fst: actual_pair.0, snd: actual_pair.1 }
            };
        let s1: &mut [u8] = s·.fst;
        let s2: &mut [u8] = s·.snd;
        let split123: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s1, snd: s2 };
        let input23: &mut [u8] = split123.snd;
        let consumed: usize = len.wrapping_sub(0usize);
        let s1s2: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
            {
                let actual_pair: (&mut [u8], &mut [u8]) = input23.split_at_mut(consumed);
                __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                { fst: actual_pair.0, snd: actual_pair.1 }
            };
        let s10: &mut [u8] = s1s2.fst;
        let s20: &mut [u8] = s1s2.snd;
        let res: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s10, snd: s20 };
        let left: &mut [u8] = res.fst;
        let right: &mut [u8] = res.snd;
        let split23: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
            { fst: left, snd: right };
        let input1: &mut [u8] = split23.fst;
        let check: [bool; 1] = [false; 1usize];
        crate::lowstar::ignore::ignore::<&[bool]>(&check);
        let mut pn: [usize; 1] = [1usize; 1usize];
        let mut pres: [bool; 1] = [true; 1usize];
        let mut ppi: [&mut [u8]; 1] = [input1; 1usize];
        let res0: bool = (&pres)[0];
        let n: usize = (&pn)[0];
        let mut cond: bool = res0 && n > 0usize;
        while
        cond
        {
            let n0: usize = (&pn)[0];
            let pi: &mut [u8] = (&ppi)[0];
            let i: usize = jump_raw_data_item(pi, 0usize);
            let s: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                {
                    let actual_pair: (&mut [u8], &mut [u8]) = pi.split_at_mut(i);
                    __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                    { fst: actual_pair.0, snd: actual_pair.1 }
                };
            let s11: &mut [u8] = s.fst;
            let s21: &mut [u8] = s.snd;
            let res1: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                { fst: s11, snd: s21 };
            let input11: &mut [u8] = res1.fst;
            let input2: &mut [u8] = res1.snd;
            let res2: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                { fst: input11, snd: input2 };
            let input110: &mut [u8] = res2.fst;
            let input20: &mut [u8] = res2.snd;
            let spl: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                { fst: input110, snd: input20 };
            let res3: &mut [u8] = spl.fst;
            let px: &mut [u8] = res3;
            let res4: bool = cbor_raw_ints_optimal(px);
            if ! res4
            { (&mut pres)[0] = false }
            else
            {
                let off1: usize = jump_header(pi, 0usize);
                let s·0: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    {
                        let actual_pair: (&mut [u8], &mut [u8]) = pi.split_at_mut(0usize);
                        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                        { fst: actual_pair.0, snd: actual_pair.1 }
                    };
                let s12: &mut [u8] = s·0.fst;
                let s22: &mut [u8] = s·0.snd;
                let split1230: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                    { fst: s12, snd: s22 };
                let input230: &mut [u8] = split1230.snd;
                let consumed0: usize = off1.wrapping_sub(0usize);
                let s1s20: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    {
                        let actual_pair: (&mut [u8], &mut [u8]) = input230.split_at_mut(consumed0);
                        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                        { fst: actual_pair.0, snd: actual_pair.1 }
                    };
                let s13: &mut [u8] = s1s20.fst;
                let s23: &mut [u8] = s1s20.snd;
                let res10: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                    { fst: s13, snd: s23 };
                let left0: &mut [u8] = res10.fst;
                let right0: &mut [u8] = res10.snd;
                let split230: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                    { fst: left0, snd: right0 };
                let input·: &mut [u8] = split230.fst;
                let res11: header = read_header(input·);
                let x: header = res11;
                let b: initial_byte_t = x.fst;
                let i0: usize =
                    if
                    b.major_type == cbor_major_type_byte_string
                    ||
                    b.major_type == cbor_major_type_text_string
                    {
                        let l: long_argument = x.snd;
                        off1.wrapping_add(argument_as_uint64(l) as usize)
                    }
                    else
                    { off1.wrapping_add(0usize) };
                let s0: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    {
                        let actual_pair: (&mut [u8], &mut [u8]) = pi.split_at_mut(i0);
                        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                        { fst: actual_pair.0, snd: actual_pair.1 }
                    };
                let s14: &mut [u8] = s0.fst;
                let s24: &mut [u8] = s0.snd;
                let res12: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                    { fst: s14, snd: s24 };
                let input111: &mut [u8] = res12.fst;
                let input21: &mut [u8] = res12.snd;
                let spl0: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                    { fst: input111, snd: input21 };
                let ph: &mut [u8] = spl0.fst;
                let pc: &[u8] = spl0.snd;
                let unused: usize = pc.len();
                crate::lowstar::ignore::ignore::<usize>(unused);
                let count: usize = jump_recursive_step_count_leaf(ph);
                (&mut pn)[0] = n0.wrapping_sub(1usize).wrapping_add(count);
                (&mut ppi)[0] = pc
            };
            let res5: bool = (&pres)[0];
            let n1: usize = (&pn)[0];
            cond = res5 && n1 > 0usize
        };
        let res1: bool = (&pres)[0];
        let check1: bool = res1;
        if ! check1
        { 0usize }
        else
        {
            let mut pn0: [usize; 1] = [1usize; 1usize];
            let mut pres0: [bool; 1] = [true; 1usize];
            let mut ppi0: [&mut [u8]; 1] = [input1; 1usize];
            let res2: bool = (&pres0)[0];
            let n0: usize = (&pn0)[0];
            let mut cond0: bool = res2 && n0 > 0usize;
            while
            cond0
            {
                let n1: usize = (&pn0)[0];
                let pi: &mut [u8] = (&ppi0)[0];
                let i: usize = jump_raw_data_item(pi, 0usize);
                let s: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    {
                        let actual_pair: (&mut [u8], &mut [u8]) = pi.split_at_mut(i);
                        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                        { fst: actual_pair.0, snd: actual_pair.1 }
                    };
                let s11: &mut [u8] = s.fst;
                let s21: &mut [u8] = s.snd;
                let res3: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                    { fst: s11, snd: s21 };
                let input11: &mut [u8] = res3.fst;
                let input2: &mut [u8] = res3.snd;
                let res4: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                    { fst: input11, snd: input2 };
                let input110: &mut [u8] = res4.fst;
                let input20: &mut [u8] = res4.snd;
                let spl: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                    __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                    { fst: input110, snd: input20 };
                let res5: &mut [u8] = spl.fst;
                let px: &mut [u8] = res5;
                let res6: bool = cbor_raw_sorted(px);
                if ! res6
                { (&mut pres0)[0] = false }
                else
                {
                    let off1: usize = jump_header(pi, 0usize);
                    let s·0: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                        {
                            let actual_pair: (&mut [u8], &mut [u8]) = pi.split_at_mut(0usize);
                            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                            { fst: actual_pair.0, snd: actual_pair.1 }
                        };
                    let s12: &mut [u8] = s·0.fst;
                    let s22: &mut [u8] = s·0.snd;
                    let split1230: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                        { fst: s12, snd: s22 };
                    let input230: &mut [u8] = split1230.snd;
                    let consumed0: usize = off1.wrapping_sub(0usize);
                    let s1s20: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                        {
                            let actual_pair: (&mut [u8], &mut [u8]) =
                                input230.split_at_mut(consumed0);
                            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                            { fst: actual_pair.0, snd: actual_pair.1 }
                        };
                    let s13: &mut [u8] = s1s20.fst;
                    let s23: &mut [u8] = s1s20.snd;
                    let res10: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                        { fst: s13, snd: s23 };
                    let left0: &mut [u8] = res10.fst;
                    let right0: &mut [u8] = res10.snd;
                    let split230: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                        { fst: left0, snd: right0 };
                    let input·: &mut [u8] = split230.fst;
                    let res11: header = read_header(input·);
                    let x: header = res11;
                    let b: initial_byte_t = x.fst;
                    let i0: usize =
                        if
                        b.major_type == cbor_major_type_byte_string
                        ||
                        b.major_type == cbor_major_type_text_string
                        {
                            let l: long_argument = x.snd;
                            off1.wrapping_add(argument_as_uint64(l) as usize)
                        }
                        else
                        { off1.wrapping_add(0usize) };
                    let s0: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                        {
                            let actual_pair: (&mut [u8], &mut [u8]) = pi.split_at_mut(i0);
                            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                            { fst: actual_pair.0, snd: actual_pair.1 }
                        };
                    let s14: &mut [u8] = s0.fst;
                    let s24: &mut [u8] = s0.snd;
                    let res12: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                        { fst: s14, snd: s24 };
                    let input111: &mut [u8] = res12.fst;
                    let input21: &mut [u8] = res12.snd;
                    let spl0: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
                        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
                        { fst: input111, snd: input21 };
                    let ph: &mut [u8] = spl0.fst;
                    let pc: &[u8] = spl0.snd;
                    let unused: usize = pc.len();
                    crate::lowstar::ignore::ignore::<usize>(unused);
                    let count: usize = jump_recursive_step_count_leaf(ph);
                    (&mut pn0)[0] = n1.wrapping_sub(1usize).wrapping_add(count);
                    (&mut ppi0)[0] = pc
                };
                let res7: bool = (&pres0)[0];
                let n2: usize = (&pn0)[0];
                cond0 = res7 && n2 > 0usize
            };
            let res3: bool = (&pres0)[0];
            let check2: bool = res3;
            if ! check2 { 0usize } else { len }
        }
    }
}

fn cbor_validate_det(input: &mut [u8]) -> usize
{
    let res: usize = cbor_validate_det·(input);
    res
}

fn cbor_parse <'a>(input: &'a mut [u8], len: usize) -> cbor_raw <'a>
{
    let s·: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        {
            let actual_pair: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
            { fst: actual_pair.0, snd: actual_pair.1 }
        };
    let s1: &mut [u8] = s·.fst;
    let s2: &mut [u8] = s·.snd;
    let split123: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s1, snd: s2 };
    let input23: &mut [u8] = split123.snd;
    let consumed: usize = len.wrapping_sub(0usize);
    let s1s2: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        {
            let actual_pair: (&mut [u8], &mut [u8]) = input23.split_at_mut(consumed);
            __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t
            { fst: actual_pair.0, snd: actual_pair.1 }
        };
    let s10: &mut [u8] = s1s2.fst;
    let s20: &mut [u8] = s1s2.snd;
    let res: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: s10, snd: s20 };
    let left: &mut [u8] = res.fst;
    let right: &mut [u8] = res.snd;
    let split23: __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t =
        __Pulse_Lib_Slice_slice·uint8_t_Pulse_Lib_Slice_slice·uint8_t { fst: left, snd: right };
    let input1: &mut [u8] = split23.fst;
    let res0: cbor_raw = cbor_read(input1);
    res0
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

pub fn uu___is_CBOR_Case_Int <'a>(projectee: cbor_raw <'a>) -> bool
{ match projectee { cbor_raw::CBOR_Case_Int { .. } => true, _ => false } }

pub fn uu___is_CBOR_Case_Simple <'a>(projectee: cbor_raw <'a>) -> bool
{ match projectee { cbor_raw::CBOR_Case_Simple { .. } => true, _ => false } }

pub fn uu___is_CBOR_Case_String <'a>(projectee: cbor_raw <'a>) -> bool
{ match projectee { cbor_raw::CBOR_Case_String { .. } => true, _ => false } }

pub fn uu___is_CBOR_Case_Tagged <'a>(projectee: cbor_raw <'a>) -> bool
{ match projectee { cbor_raw::CBOR_Case_Tagged { .. } => true, _ => false } }

pub fn uu___is_CBOR_Case_Array <'a>(projectee: cbor_raw <'a>) -> bool
{ match projectee { cbor_raw::CBOR_Case_Array { .. } => true, _ => false } }

pub fn uu___is_CBOR_Case_Map <'a>(projectee: cbor_raw <'a>) -> bool
{ match projectee { cbor_raw::CBOR_Case_Map { .. } => true, _ => false } }

pub fn uu___is_CBOR_Case_Serialized_Tagged <'a>(projectee: cbor_raw <'a>) -> bool
{ match projectee { cbor_raw::CBOR_Case_Serialized_Tagged { .. } => true, _ => false } }

pub fn uu___is_CBOR_Case_Serialized_Array <'a>(projectee: cbor_raw <'a>) -> bool
{ match projectee { cbor_raw::CBOR_Case_Serialized_Array { .. } => true, _ => false } }

pub fn uu___is_CBOR_Case_Serialized_Map <'a>(projectee: cbor_raw <'a>) -> bool
{ match projectee { cbor_raw::CBOR_Case_Serialized_Map { .. } => true, _ => false } }

pub type cbor_array_iterator <'a> = cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>;

pub type cbor_map_iterator <'a> = cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>;

pub type cbor_det_t <'a> = cbor_raw <'a>;

pub type cbor_det_map_entry_t <'a> = cbor_map_entry <'a>;

pub type cbor_det_array_iterator_t <'a> = cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>;

pub type cbor_det_map_iterator_t <'a> =
cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>;

pub fn cbor_det_validate(input: &mut [u8]) -> usize
{
    let res: usize = cbor_validate_det(input);
    res
}

pub fn cbor_det_parse <'a>(input: &'a mut [u8], len: usize) -> cbor_raw <'a>
{
    let res: cbor_raw = cbor_parse(input, len);
    res
}

pub fn cbor_det_size <'a>(x: cbor_raw <'a>, bound: usize) -> usize
{
    let res: usize = cbor_size(x, bound);
    res
}

pub fn cbor_det_serialize <'a>(x: cbor_raw <'a>, output: &'a mut [u8]) -> usize
{
    let res: usize = cbor_serialize(x, output);
    res
}

pub fn cbor_det_mk_simple_value <'a>(v: u8) -> cbor_raw <'a>
{ cbor_raw::CBOR_Case_Simple { v } }

pub fn cbor_det_mk_int64 <'a>(ty: u8, v: u64) -> cbor_raw <'a>
{
    let res: cbor_int =
        cbor_int
        {
            cbor_int_type: ty,
            cbor_int_size: (mk_raw_uint64(v)).size,
            cbor_int_value: (mk_raw_uint64(v)).value
        };
    let resi: cbor_int = res;
    let res0: cbor_raw = cbor_raw::CBOR_Case_Int { v: resi };
    res0
}

pub fn cbor_det_mk_string <'a>(ty: u8, s: &'a mut [u8]) -> cbor_raw <'a>
{
    let len64: raw_uint64 = mk_raw_uint64(s.len() as u64);
    let ress: cbor_string =
        cbor_string { cbor_string_type: ty, cbor_string_size: len64.size, cbor_string_ptr: s };
    cbor_raw::CBOR_Case_String { v: ress }
}

pub fn cbor_det_mk_tagged <'a>(tag: u64, r: &'a [cbor_raw <'a>]) -> cbor_raw <'a>
{
    let tag64: raw_uint64 = mk_raw_uint64(tag);
    let res·: cbor_tagged = cbor_tagged { cbor_tagged_tag: tag64, cbor_tagged_ptr: r };
    cbor_raw::CBOR_Case_Tagged { v: res· }
}

pub fn cbor_det_mk_array <'a>(a: &'a [cbor_raw <'a>], len: u64) -> cbor_raw <'a>
{
    let len64: raw_uint64 = mk_raw_uint64(len);
    let res·: cbor_array = cbor_array { cbor_array_length: len64, cbor_array_ptr: a };
    cbor_raw::CBOR_Case_Array { v: res· }
}

fn cbor_raw_compare <'a>(x1: cbor_raw <'a>, x2: cbor_raw <'a>) -> i16
{ impl_cbor_compare(x1, x2) }

fn cbor_map_entry_raw_compare <'a>(x1: cbor_map_entry <'a>, x2: cbor_map_entry <'a>) -> i16
{
    let res: i16 = cbor_raw_compare(x1.cbor_map_entry_key, x2.cbor_map_entry_key);
    res
}

pub(crate) fn cbor_raw_sort_aux(a: &mut [cbor_map_entry], lo: usize, hi: usize) -> bool
{
    let len: usize = hi.wrapping_sub(lo);
    if len < 2usize
    { true }
    else
    {
        let len_half: usize = len.wrapping_div(2usize);
        let mi: usize = lo.wrapping_add(len_half);
        let res: bool = cbor_raw_sort_aux(a, lo, mi);
        if ! res
        { false }
        else
        {
            let res1: bool = cbor_raw_sort_aux(a, mi, hi);
            if ! res1
            { false }
            else
            {
                let mut pi1: [usize; 1] = [lo; 1usize];
                let mut pi2: [usize; 1] = [mi; 1usize];
                let mut pres: [bool; 1] = [true; 1usize];
                let i1: usize = (&pi1)[0];
                let i2: usize = (&pi2)[0];
                let res2: bool = (&pres)[0];
                let mut cond: bool = res2 && ! (i1 == i2 || i2 == hi);
                while
                cond
                {
                    let i10: usize = (&pi1)[0];
                    let x1: &cbor_map_entry = &a[i10];
                    let i20: usize = (&pi2)[0];
                    let x2: &cbor_map_entry = &a[i20];
                    let comp: i16 = cbor_map_entry_raw_compare(*x1, *x2);
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
                        let i1·: usize =
                            if i10 == i20
                            { i2· }
                            else if i20 == i2·
                            { i10 }
                            else
                            {
                                let mut pn: [usize; 1] = [i2·.wrapping_sub(i10); 1usize];
                                let mut pl: [usize; 1] = [i20.wrapping_sub(i10); 1usize];
                                let l3: usize = (&pl)[0];
                                let mut cond0: bool = l3 > 0usize;
                                while
                                cond0
                                {
                                    let n: usize = (&pn)[0];
                                    let l30: usize = (&pl)[0];
                                    let l·: usize = n.wrapping_rem(l30);
                                    (&mut pn)[0] = l30;
                                    (&mut pl)[0] = l·;
                                    let l31: usize = (&pl)[0];
                                    cond0 = l31 > 0usize
                                };
                                let d: usize = (&pn)[0];
                                let q: usize = i2·.wrapping_sub(i10).wrapping_div(d);
                                let mut pi: [usize; 1] = [i10; 1usize];
                                let i: usize = (&pi)[0];
                                let mut cond1: bool = i.wrapping_sub(i10) < d;
                                while
                                cond1
                                {
                                    let i0: usize = (&pi)[0];
                                    let save: &cbor_map_entry = &a[i0];
                                    let mut pj: [usize; 1] = [0usize; 1usize];
                                    let mut pidx: [usize; 1] = [i0; 1usize];
                                    let j: usize = (&pj)[0];
                                    let mut cond2: bool = j < q.wrapping_sub(1usize);
                                    while
                                    cond2
                                    {
                                        let j0: usize = (&pj)[0];
                                        let idx: usize = (&pidx)[0];
                                        let idx·: usize =
                                            if idx.wrapping_sub(i10) >= i2·.wrapping_sub(i20)
                                            { idx.wrapping_sub(i2·.wrapping_sub(i20)) }
                                            else
                                            { idx.wrapping_add(i20.wrapping_sub(i10)) };
                                        let x: &cbor_map_entry = &a[idx·];
                                        let j·: usize = j0.wrapping_add(1usize);
                                        a[idx] = *x;
                                        (&mut pj)[0] = j·;
                                        (&mut pidx)[0] = idx·;
                                        let j1: usize = (&pj)[0];
                                        cond2 = j1 < q.wrapping_sub(1usize)
                                    };
                                    let idx: usize = (&pidx)[0];
                                    a[idx] = *save;
                                    let i·: usize = i0.wrapping_add(1usize);
                                    (&mut pi)[0] = i·;
                                    let i3: usize = (&pi)[0];
                                    cond1 = i3.wrapping_sub(i10) < d
                                };
                                i10.wrapping_add(i2·.wrapping_sub(i20))
                            };
                        (&mut pi1)[0] = i1·;
                        (&mut pi2)[0] = i2·
                    };
                    let i11: usize = (&pi1)[0];
                    let i21: usize = (&pi2)[0];
                    let res20: bool = (&pres)[0];
                    cond = res20 && ! (i11 == i21 || i21 == hi)
                };
                let res20: bool = (&pres)[0];
                res20
            }
        }
    }
}

fn cbor_raw_sort(a: &mut [cbor_map_entry], len: usize) -> bool
{
    let res: bool = cbor_raw_sort_aux(a, 0usize, len);
    res
}

pub fn cbor_det_mk_map <'a>(a: &'a mut [cbor_map_entry <'a>], len: u64) -> cbor_raw <'a>
{
    crate::lowstar::ignore::ignore::<bool>(cbor_raw_sort(a, len as usize));
    let raw_len: raw_uint64 = mk_raw_uint64(len);
    let res·: cbor_map = cbor_map { cbor_map_length: raw_len, cbor_map_ptr: a };
    cbor_raw::CBOR_Case_Map { v: res· }
}

pub fn cbor_det_equal <'a>(x1: cbor_raw <'a>, x2: cbor_raw <'a>) -> bool
{
    let comp: i16 = impl_cbor_compare(x1, x2);
    comp == 0i16
}

pub fn cbor_det_major_type <'a>(x: cbor_raw <'a>) -> u8
{
    let res: u8 = impl_major_type(x);
    res
}

pub fn cbor_det_read_simple_value <'a>(x: cbor_raw <'a>) -> u8
{
    match x
    { cbor_raw::CBOR_Case_Simple { v: v1 } => v1, _ => panic!("Incomplete pattern matching") }
}

pub fn cbor_det_read_uint64 <'a>(x: cbor_raw <'a>) -> u64
{
    let c·: cbor_int =
        match x
        { cbor_raw::CBOR_Case_Int { v: v1 } => v1, _ => panic!("Incomplete pattern matching") };
    let res: raw_uint64 = raw_uint64 { size: c·.cbor_int_size, value: c·.cbor_int_value };
    res.value
}

pub fn cbor_det_get_string <'a>(x: cbor_raw <'a>) -> &'a [u8]
{
    let c·: cbor_string =
        match x
        { cbor_raw::CBOR_Case_String { v: v1 } => v1, _ => panic!("Incomplete pattern matching") };
    c·.cbor_string_ptr
}

pub fn cbor_det_get_tagged_tag <'a>(x: cbor_raw <'a>) -> u64
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

pub fn cbor_det_get_tagged_payload <'a>(x: cbor_raw <'a>) -> cbor_raw <'a>
{
    let res: cbor_raw = cbor_match_tagged_get_payload(x);
    res
}

pub fn cbor_det_get_array_length <'a>(x: cbor_raw <'a>) -> u64
{
    let res: raw_uint64 =
        match x
        {
            cbor_raw::CBOR_Case_Array { v: c· } => c·.cbor_array_length,
            cbor_raw::CBOR_Case_Serialized_Array { v: c· } => c·.cbor_serialized_header,
            _ => panic!("Incomplete pattern matching")
        };
    res.value
}

pub fn cbor_det_array_iterator_start <'a>(x: cbor_raw <'a>) ->
    cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
    <'a>
{
    let res: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = cbor_array_iterator_init(x);
    res
}

pub fn cbor_det_array_iterator_is_empty <'a>(
    x: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>
) ->
    bool
{
    let res: bool = cbor_array_iterator_is_empty(x);
    res
}

pub fn cbor_det_array_iterator_next <'a>(
    x: &'a mut [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw <'a>]
) ->
    cbor_raw
    <'a>
{
    let res: cbor_raw = cbor_array_iterator_next(x);
    res
}

pub fn cbor_det_get_map_length <'a>(x: cbor_raw <'a>) -> u64
{
    let res: raw_uint64 =
        match x
        {
            cbor_raw::CBOR_Case_Map { v: c· } => c·.cbor_map_length,
            cbor_raw::CBOR_Case_Serialized_Map { v: c· } => c·.cbor_serialized_header,
            _ => panic!("Incomplete pattern matching")
        };
    res.value
}

pub fn cbor_det_map_iterator_start <'a>(x: cbor_raw <'a>) ->
    cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry
    <'a>
{
    let res: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry = cbor_map_iterator_init(x);
    res
}

pub fn cbor_det_map_iterator_is_empty <'a>(
    x: cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>
) ->
    bool
{
    let res: bool = cbor_map_iterator_is_empty(x);
    res
}

pub fn cbor_det_map_iterator_next <'a>(
    x: &'a mut [cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry <'a>]
) ->
    cbor_map_entry
    <'a>
{
    let res: cbor_map_entry = cbor_map_iterator_next(x);
    res
}
