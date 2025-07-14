#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub fn mk_int(i: i32) -> crate::coseformat::evercddl_int_pretty
{
    if i < 0i32
    {
        let k: i32 = -1i32.wrapping_sub(i);
        let j: u64 = k as u64;
        crate::coseformat::evercddl_int_pretty::Mkevercddl_int_pretty1 { _x0: j }
    }
    else
    {
        let j: u64 = i as u64;
        crate::coseformat::evercddl_int_pretty::Mkevercddl_int_pretty0 { _x0: j }
    }
}

pub type ser_to = ();

pub type to_be_signed_spec = ();

pub fn create_sig(
    privkey: &[u8],
    phdr: crate::coseformat::evercddl_empty_or_serialized_map_pretty,
    aad: &[u8],
    payload: &[u8],
    sigbuf: &mut [u8]
)
{
    let sz: usize = 1024usize;
    let mut arr: Box<[u8]> = vec![0u8; sz].into_boxed_slice();
    let outbuf: &mut [u8] = &mut arr;
    let sig_struct: crate::coseformat::evercddl_Sig_structure_pretty =
        crate::coseformat::evercddl_Sig_structure_pretty
        {
            context: crate::coseformat::evercddl_int_tags::Inr,
            body_protected: phdr,
            _x0:
            crate::coseformat::either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·::Inr
            { v: (aad,payload) }
        };
    let res: usize = crate::coseformat::serialize_Sig_structure(sig_struct, outbuf);
    let written: usize = res;
    if written == 0usize
    { crate::commonabort::abort() }
    else
    {
        let res0: &[u8] = &outbuf[0usize..written];
        let tbs: &[u8] = res0;
        crate::ed25519::sign(sigbuf, privkey, tbs)
    }
}

pub fn dummy_map_val <'a>() ->
    (crate::coseformat::evercddl_label_pretty <'a>, crate::cbordetveraux::cbor_raw <'a>)
{
    (
        crate::coseformat::evercddl_label_pretty::Mkevercddl_label_pretty0
        { _x0: crate::coseformat::evercddl_int_pretty::Mkevercddl_int_pretty0 { _x0: 0u64 } },crate::cbordetver::dummy_cbor_det_t(

        )
    )
}

pub fn mk_phdrs <'a>(
    alg: i32,
    rest:
    &'a [(crate::coseformat::evercddl_label_pretty <'a>, crate::cbordetveraux::cbor_raw <'a>)]
) ->
    crate::coseformat::evercddl_empty_or_serialized_map_pretty
    <'a>
{
    let alg·: crate::coseformat::evercddl_int_pretty = mk_int(alg);
    let rest2: &[(crate::coseformat::evercddl_label_pretty, crate::cbordetveraux::cbor_raw)] =
        rest;
    crate::coseformat::evercddl_empty_or_serialized_map_pretty::Mkevercddl_empty_or_serialized_map_pretty0
    {
        _x0:
        crate::coseformat::evercddl_header_map_pretty
        {
            intkey1:
            crate::coseformat::option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty::Some
            { v: crate::coseformat::evercddl_label::Inl { v: alg· } },
            intkey2:
            crate::coseformat::option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env24_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env24_type_1_pretty::None,
            intkey3:
            crate::coseformat::option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty::None,
            intkey4: crate::coseformat::option__COSE_Format_evercddl_bstr_pretty::None,
            _x0:
            crate::coseformat::either__··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty····FStar_Pervasives_either·CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty··CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty·_FStar_Pervasives_either···COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty····FStar_Pervasives_either·CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty··CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty····FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty····FStar_Pervasives_either·CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty··CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty·::Inr
            {
                v:
                crate::coseformat::either__··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty····FStar_Pervasives_either·CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty··CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty·_··FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty····FStar_Pervasives_either·CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty··CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty·::Inr
                {
                    v:
                    (
                        (
                            crate::coseformat::option__COSE_Format_evercddl_everparsenomatch_pretty::None,crate::coseformat::option__COSE_Format_evercddl_everparsenomatch_pretty::None
                        ),crate::coseformat::either__CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty::Inl
                        { v: rest2 }
                    )
                }
            }
        }
    }
}

pub type sign1_spec = ();

pub fn sign1 <'a>(
    privkey: &'a [u8],
    uhdr: crate::coseformat::evercddl_header_map_pretty <'a>,
    aad: &'a [u8],
    payload: &'a [u8],
    outbuf: &'a mut [u8]
) ->
    &'a [u8]
{
    let alg: i32 = -8i32;
    let
    phdrauxbuf: [(crate::coseformat::evercddl_label_pretty, crate::cbordetveraux::cbor_raw); 0]
    =
        [dummy_map_val(); 0usize];
    let alg·: crate::coseformat::evercddl_int_pretty = mk_int(alg);
    let rest2: &[(crate::coseformat::evercddl_label_pretty, crate::cbordetveraux::cbor_raw)] =
        &phdrauxbuf;
    let phdr: crate::coseformat::evercddl_empty_or_serialized_map_pretty =
        crate::coseformat::evercddl_empty_or_serialized_map_pretty::Mkevercddl_empty_or_serialized_map_pretty0
        {
            _x0:
            crate::coseformat::evercddl_header_map_pretty
            {
                intkey1:
                crate::coseformat::option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty::Some
                { v: crate::coseformat::evercddl_label::Inl { v: alg· } },
                intkey2:
                crate::coseformat::option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env24_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env24_type_1_pretty::None,
                intkey3:
                crate::coseformat::option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty::None,
                intkey4: crate::coseformat::option__COSE_Format_evercddl_bstr_pretty::None,
                _x0:
                crate::coseformat::either__··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty····FStar_Pervasives_either·CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty··CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty·_FStar_Pervasives_either···COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty····FStar_Pervasives_either·CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty··CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty····FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty····FStar_Pervasives_either·CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty··CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty·::Inr
                {
                    v:
                    crate::coseformat::either__··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty····FStar_Pervasives_either·CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty··CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty·_··FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty····FStar_Pervasives_either·CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty··CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty·::Inr
                    {
                        v:
                        (
                            (
                                crate::coseformat::option__COSE_Format_evercddl_everparsenomatch_pretty::None,crate::coseformat::option__COSE_Format_evercddl_everparsenomatch_pretty::None
                            ),crate::coseformat::either__CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty::Inl
                            { v: rest2 }
                        )
                    }
                }
            }
        };
    let mut sigbuf: [u8; 64] = [0u8; 64usize];
    let sigbuf2: &mut [u8] = &mut sigbuf;
    create_sig(privkey, phdr, aad, payload, sigbuf2);
    let res: usize =
        crate::coseformat::serialize_COSE_Sign1_Tagged(
            crate::coseformat::evercddl_COSE_Sign1_pretty
            {
                protected: phdr,
                unprotected: uhdr,
                payload:
                crate::coseformat::either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty::Inl
                { v: payload },
                signature: sigbuf2
            },
            outbuf
        );
    let outbuf_sz: usize = res;
    if outbuf_sz == 0usize
    {
        crate::commonabort::abort();
        outbuf
    }
    else
    {
        let res0: &[u8] = &outbuf[0usize..outbuf_sz];
        let out: &[u8] = res0;
        out
    }
}

pub fn sign1_simple <'a>(privkey: &'a [u8], payload: &'a [u8], outbuf: &'a mut [u8]) ->
    &'a [u8]
{
    let
    uhdrauxbuf: [(crate::coseformat::evercddl_label_pretty, crate::cbordetveraux::cbor_raw); 0]
    =
        [dummy_map_val(); 0usize];
    let rest2: &[(crate::coseformat::evercddl_label_pretty, crate::cbordetveraux::cbor_raw)] =
        &uhdrauxbuf;
    let uhdr: crate::coseformat::evercddl_header_map_pretty =
        crate::coseformat::evercddl_header_map_pretty
        {
            intkey1:
            crate::coseformat::option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty::None,
            intkey2:
            crate::coseformat::option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env24_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env24_type_1_pretty::None,
            intkey3:
            crate::coseformat::option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty::None,
            intkey4: crate::coseformat::option__COSE_Format_evercddl_bstr_pretty::None,
            _x0:
            crate::coseformat::either__··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty····FStar_Pervasives_either·CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty··CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty·_FStar_Pervasives_either···COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty····FStar_Pervasives_either·CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty··CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty····FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty····FStar_Pervasives_either·CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty··CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty·::Inr
            {
                v:
                crate::coseformat::either__··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty····FStar_Pervasives_either·CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty··CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty·_··FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty····FStar_Pervasives_either·CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty··CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty·::Inr
                {
                    v:
                    (
                        (
                            crate::coseformat::option__COSE_Format_evercddl_everparsenomatch_pretty::None,crate::coseformat::option__COSE_Format_evercddl_everparsenomatch_pretty::None
                        ),crate::coseformat::either__CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty::Inl
                        { v: rest2 }
                    )
                }
            }
        };
    let aadbuf: [u8; 0] = [0u8; 0usize];
    let aadslice: &[u8] = &aadbuf;
    let alg: i32 = -8i32;
    let
    phdrauxbuf: [(crate::coseformat::evercddl_label_pretty, crate::cbordetveraux::cbor_raw); 0]
    =
        [dummy_map_val(); 0usize];
    let alg·: crate::coseformat::evercddl_int_pretty = mk_int(alg);
    let rest20: &[(crate::coseformat::evercddl_label_pretty, crate::cbordetveraux::cbor_raw)] =
        &phdrauxbuf;
    let phdr: crate::coseformat::evercddl_empty_or_serialized_map_pretty =
        crate::coseformat::evercddl_empty_or_serialized_map_pretty::Mkevercddl_empty_or_serialized_map_pretty0
        {
            _x0:
            crate::coseformat::evercddl_header_map_pretty
            {
                intkey1:
                crate::coseformat::option__FStar_Pervasives_either·COSE_Format_evercddl_int_pretty·COSE_Format_evercddl_tstr_pretty::Some
                { v: crate::coseformat::evercddl_label::Inl { v: alg· } },
                intkey2:
                crate::coseformat::option__FStar_Pervasives_either·CDDL_Pulse_Types_slice·COSE_Format_aux_env24_type_1_pretty·CDDL_Pulse_Parse_ArrayGroup_array_iterator_t·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_raw·COSE_Format_aux_env24_type_1_pretty::None,
                intkey3:
                crate::coseformat::option__FStar_Pervasives_either·COSE_Format_evercddl_tstr_pretty·COSE_Format_evercddl_int_pretty::None,
                intkey4: crate::coseformat::option__COSE_Format_evercddl_bstr_pretty::None,
                _x0:
                crate::coseformat::either__··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty····FStar_Pervasives_either·CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty··CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty·_FStar_Pervasives_either···COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty····FStar_Pervasives_either·CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty··CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty····FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty····FStar_Pervasives_either·CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty··CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty·::Inr
                {
                    v:
                    crate::coseformat::either__··COSE_Format_evercddl_bstr_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty····FStar_Pervasives_either·CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty··CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty·_··FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty···FStar_Pervasives_Native_option·COSE_Format_evercddl_everparsenomatch_pretty····FStar_Pervasives_either·CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty··CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty·::Inr
                    {
                        v:
                        (
                            (
                                crate::coseformat::option__COSE_Format_evercddl_everparsenomatch_pretty::None,crate::coseformat::option__COSE_Format_evercddl_everparsenomatch_pretty::None
                            ),crate::coseformat::either__CDDL_Pulse_Types_slice··COSE_Format_aux_env24_type_2_pretty···COSE_Format_aux_env24_type_3_pretty·_CDDL_Pulse_Parse_MapGroup_map_iterator_t·CBOR_Pulse_Raw_Type_cbor_raw·CBOR_Pulse_Raw_Type_cbor_map_entry·CBOR_Pulse_Raw_Iterator_cbor_raw_iterator·CBOR_Pulse_Raw_Type_cbor_map_entry·COSE_Format_aux_env24_type_2_pretty·COSE_Format_aux_env24_type_3_pretty::Inl
                            { v: rest20 }
                        )
                    }
                }
            }
        };
    let mut sigbuf: [u8; 64] = [0u8; 64usize];
    let sigbuf2: &mut [u8] = &mut sigbuf;
    create_sig(privkey, phdr, aadslice, payload, sigbuf2);
    let res: usize =
        crate::coseformat::serialize_COSE_Sign1_Tagged(
            crate::coseformat::evercddl_COSE_Sign1_pretty
            {
                protected: phdr,
                unprotected: uhdr,
                payload:
                crate::coseformat::either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty::Inl
                { v: payload },
                signature: sigbuf2
            },
            outbuf
        );
    let outbuf_sz: usize = res;
    let _bind_c: &[u8] =
        if outbuf_sz == 0usize
        {
            crate::commonabort::abort();
            outbuf
        }
        else
        {
            let res0: &[u8] = &outbuf[0usize..outbuf_sz];
            let out: &[u8] = res0;
            out
        };
    let res0: &[u8] = _bind_c;
    res0
}

pub fn verify_sig(
    pubkey: &[u8],
    phdr: crate::coseformat::evercddl_empty_or_serialized_map_pretty,
    aad: &[u8],
    payload: &[u8],
    sigbuf: &[u8]
) ->
    bool
{
    let sz: usize = 1024usize;
    let mut arr: Box<[u8]> = vec![0u8; sz].into_boxed_slice();
    let outbuf: &mut [u8] = &mut arr;
    let sig_struct: crate::coseformat::evercddl_Sig_structure_pretty =
        crate::coseformat::evercddl_Sig_structure_pretty
        {
            context: crate::coseformat::evercddl_int_tags::Inr,
            body_protected: phdr,
            _x0:
            crate::coseformat::either__·COSE_Format_evercddl_empty_or_serialized_map_pretty····COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty··_·COSE_Format_evercddl_bstr_pretty···COSE_Format_evercddl_bstr_pretty·::Inr
            { v: (aad,payload) }
        };
    let res: usize = crate::coseformat::serialize_Sig_structure(sig_struct, outbuf);
    let written: usize = res;
    if written == 0usize
    {
        crate::commonabort::abort();
        false
    }
    else
    {
        let res0: &[u8] = &outbuf[0usize..written];
        let tbs: &[u8] = res0;
        let success: bool = crate::ed25519::verify(pubkey, tbs, sigbuf);
        success
    }
}

pub type good_signature = ();

fn uu___is_Inl__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty(
    projectee:
    crate::coseformat::either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty
) ->
    bool
{
    match projectee
    {
        crate::coseformat::either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty::Inl
        { .. }
        => true,
        _ => false
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__Pulse_Lib_Slice_slice·uint8_t <'a>
{
    None,
    Some { v: &'a [u8] }
}

pub fn verify1 <'a>(pubkey: &'a [u8], aad: &'a [u8], msg: &'a [u8]) ->
    option__Pulse_Lib_Slice_slice·uint8_t
    <'a>
{
    let
    res:
    crate::coseformat::option__·COSE_Format_evercddl_COSE_Sign1_Tagged_pretty···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::coseformat::validate_and_parse_COSE_Sign1_Tagged(msg);
    match res
    {
        crate::coseformat::option__·COSE_Format_evercddl_COSE_Sign1_Tagged_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__Pulse_Lib_Slice_slice·uint8_t::None,
        crate::coseformat::option__·COSE_Format_evercddl_COSE_Sign1_Tagged_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: res1 }
        =>
          {
              let x: crate::coseformat::evercddl_COSE_Sign1_pretty = res1.0;
              let rem: &[u8] = res1.1;
              if
              rem.len() == 0usize
              &&
              uu___is_Inl__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty(
                  x.payload
              )
              {
                  let sig: &[u8] = x.signature;
                  let success: bool =
                      if sig.len() == 64usize
                      {
                          let success: bool =
                              verify_sig(
                                  pubkey,
                                  x.protected,
                                  aad,
                                  match x.payload
                                  {
                                      crate::coseformat::either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty::Inl
                                      { v }
                                      => v,
                                      _ => panic!("Incomplete pattern matching")
                                  },
                                  sig
                              );
                          success
                      }
                      else
                      { false };
                  if success
                  {
                      let payload: &[u8] =
                          match x.payload
                          {
                              crate::coseformat::either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty::Inl
                              { v }
                              => v,
                              _ => panic!("Incomplete pattern matching")
                          };
                      option__Pulse_Lib_Slice_slice·uint8_t::Some { v: payload }
                  }
                  else
                  { option__Pulse_Lib_Slice_slice·uint8_t::None }
              }
              else
              { option__Pulse_Lib_Slice_slice·uint8_t::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn verify1_simple <'a>(pubkey: &'a [u8], msg: &'a [u8]) ->
    option__Pulse_Lib_Slice_slice·uint8_t
    <'a>
{
    let aadbuf: [u8; 0] = [0u8; 0usize];
    let aadslice: &[u8] = &aadbuf;
    let
    res:
    crate::coseformat::option__·COSE_Format_evercddl_COSE_Sign1_Tagged_pretty···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::coseformat::validate_and_parse_COSE_Sign1_Tagged(msg);
    match res
    {
        crate::coseformat::option__·COSE_Format_evercddl_COSE_Sign1_Tagged_pretty···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__Pulse_Lib_Slice_slice·uint8_t::None,
        crate::coseformat::option__·COSE_Format_evercddl_COSE_Sign1_Tagged_pretty···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: res1 }
        =>
          {
              let x: crate::coseformat::evercddl_COSE_Sign1_pretty = res1.0;
              let rem: &[u8] = res1.1;
              if
              rem.len() == 0usize
              &&
              uu___is_Inl__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty(
                  x.payload
              )
              {
                  let sig: &[u8] = x.signature;
                  let success: bool =
                      if sig.len() == 64usize
                      {
                          let success: bool =
                              verify_sig(
                                  pubkey,
                                  x.protected,
                                  aadslice,
                                  match x.payload
                                  {
                                      crate::coseformat::either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty::Inl
                                      { v }
                                      => v,
                                      _ => panic!("Incomplete pattern matching")
                                  },
                                  sig
                              );
                          success
                      }
                      else
                      { false };
                  if success
                  {
                      let payload: &[u8] =
                          match x.payload
                          {
                              crate::coseformat::either__COSE_Format_evercddl_bstr_pretty_COSE_Format_evercddl_nil_pretty::Inl
                              { v }
                              => v,
                              _ => panic!("Incomplete pattern matching")
                          };
                      option__Pulse_Lib_Slice_slice·uint8_t::Some { v: payload }
                  }
                  else
                  { option__Pulse_Lib_Slice_slice·uint8_t::None }
              }
              else
              { option__Pulse_Lib_Slice_slice·uint8_t::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}
