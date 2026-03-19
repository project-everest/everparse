#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub fn mk_int(i: i32) -> crate::coseformat::evercddl_int
{
    if i < 0i32
    {
        let k: i32 = -1i32.wrapping_sub(i);
        let j: u64 = k as u64;
        crate::coseformat::evercddl_int::Mkevercddl_int1 { _x0: j }
    }
    else
    {
        let j: u64 = i as u64;
        crate::coseformat::evercddl_int::Mkevercddl_int0 { _x0: j }
    }
}

pub type ser_to = ();

pub type to_be_signed_spec = ();

pub fn create_sig(
    privkey: &[u8],
    phdr: crate::coseformat::empty_or_serialized_map,
    aad: &[u8],
    payload: &[u8],
    sigbuf: &mut [u8]
)
{
    let sz: usize = 1024usize;
    let mut arr: Box<[u8]> = vec![0u8; sz].into_boxed_slice();
    let outbuf: &mut [u8] = &mut arr;
    let sig_struct: crate::coseformat::sig_structure =
        crate::coseformat::sig_structure
        {
            context: crate::coseformat::evercddl_int_ugly_tags::Inr,
            body_protected: phdr,
            _x0:
            crate::coseformat::either__·COSE_Format_empty_or_serialized_map····COSE_Format_bstr···COSE_Format_bstr··_·COSE_Format_bstr···COSE_Format_bstr·::Inr
            { v: (aad,payload) }
        };
    let written: usize = crate::coseformat::serialize_sig_structure(sig_struct, outbuf);
    if written == 0usize
    { crate::commonabort::abort() }
    else
    {
        let res: &[u8] = &outbuf[0usize..written];
        let tbs: &[u8] = res;
        crate::ed25519::sign(sigbuf, privkey, tbs)
    }
}

pub fn dummy_map_val <'a>() ->
    (crate::coseformat::evercddl_label <'a>, crate::cbordetveraux::cbor_raw <'a>)
{
    (
        crate::coseformat::evercddl_label::Mkevercddl_label0
        { _x0: crate::coseformat::evercddl_int::Mkevercddl_int0 { _x0: 0u64 } },crate::cbordetver::dummy_cbor_det_t(

        )
    )
}

pub fn mk_phdrs <'a>(
    alg: i32,
    rest: &'a [(crate::coseformat::evercddl_label <'a>, crate::cbordetveraux::cbor_raw <'a>)]
) ->
    crate::coseformat::empty_or_serialized_map
    <'a>
{
    let alg·: crate::coseformat::evercddl_int = mk_int(alg);
    let rest2: &[(crate::coseformat::evercddl_label, crate::cbordetveraux::cbor_raw)] = rest;
    crate::coseformat::empty_or_serialized_map::Mkempty_or_serialized_map0
    {
        _x0:
        crate::coseformat::header_map
        {
            intkey1:
            crate::coseformat::option__COSE_Format_evercddl_label_ugly::Some
            { v: crate::coseformat::evercddl_label_ugly::Inl { v: alg· } },
            intkey2:
            crate::coseformat::option__FStar_Pervasives_either__CDDL_Pulse_Types_slice__COSE_Format_aux_env34_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env34_type_1::None,
            intkey3: crate::coseformat::option__COSE_Format_aux_env29_type_1_ugly::None,
            intkey4: crate::coseformat::option__COSE_Format_bstr::None,
            _x0:
            crate::coseformat::either__·COSE_Format_bstr···FStar_Pervasives_Native_option__COSE_Format_everparsenomatch·_FStar_Pervasives_either__·COSE_Format_bstr···FStar_Pervasives_Native_option__COSE_Format_everparsenomatch·_·FStar_Pervasives_Native_option__COSE_Format_everparsenomatch···FStar_Pervasives_Native_option__COSE_Format_everparsenomatch·::Inr
            {
                v:
                crate::coseformat::either__·COSE_Format_bstr···FStar_Pervasives_Native_option__COSE_Format_everparsenomatch·_·FStar_Pervasives_Native_option__COSE_Format_everparsenomatch···FStar_Pervasives_Native_option__COSE_Format_everparsenomatch·::Inr
                {
                    v:
                    (
                        crate::coseformat::option__COSE_Format_everparsenomatch::None,crate::coseformat::option__COSE_Format_everparsenomatch::None
                    )
                }
            },
            _x1:
            crate::coseformat::either__CDDL_Pulse_Types_slice__·COSE_Format_evercddl_label···COSE_Format_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_values::Inl
            { v: rest2 }
        }
    }
}

pub type sign1_spec = ();

pub fn sign1 <'a>(
    privkey: &'a [u8],
    uhdr: crate::coseformat::header_map <'a>,
    aad: &'a [u8],
    payload: &'a [u8],
    outbuf: &'a mut [u8]
) ->
    &'a [u8]
{
    let alg: i32 = -8i32;
    let phdrauxbuf: [(crate::coseformat::evercddl_label, crate::cbordetveraux::cbor_raw); 0] =
        [dummy_map_val(); 0usize];
    let alg·: crate::coseformat::evercddl_int = mk_int(alg);
    let rest2: &[(crate::coseformat::evercddl_label, crate::cbordetveraux::cbor_raw)] =
        &phdrauxbuf;
    let phdr: crate::coseformat::empty_or_serialized_map =
        crate::coseformat::empty_or_serialized_map::Mkempty_or_serialized_map0
        {
            _x0:
            crate::coseformat::header_map
            {
                intkey1:
                crate::coseformat::option__COSE_Format_evercddl_label_ugly::Some
                { v: crate::coseformat::evercddl_label_ugly::Inl { v: alg· } },
                intkey2:
                crate::coseformat::option__FStar_Pervasives_either__CDDL_Pulse_Types_slice__COSE_Format_aux_env34_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env34_type_1::None,
                intkey3: crate::coseformat::option__COSE_Format_aux_env29_type_1_ugly::None,
                intkey4: crate::coseformat::option__COSE_Format_bstr::None,
                _x0:
                crate::coseformat::either__·COSE_Format_bstr···FStar_Pervasives_Native_option__COSE_Format_everparsenomatch·_FStar_Pervasives_either__·COSE_Format_bstr···FStar_Pervasives_Native_option__COSE_Format_everparsenomatch·_·FStar_Pervasives_Native_option__COSE_Format_everparsenomatch···FStar_Pervasives_Native_option__COSE_Format_everparsenomatch·::Inr
                {
                    v:
                    crate::coseformat::either__·COSE_Format_bstr···FStar_Pervasives_Native_option__COSE_Format_everparsenomatch·_·FStar_Pervasives_Native_option__COSE_Format_everparsenomatch···FStar_Pervasives_Native_option__COSE_Format_everparsenomatch·::Inr
                    {
                        v:
                        (
                            crate::coseformat::option__COSE_Format_everparsenomatch::None,crate::coseformat::option__COSE_Format_everparsenomatch::None
                        )
                    }
                },
                _x1:
                crate::coseformat::either__CDDL_Pulse_Types_slice__·COSE_Format_evercddl_label···COSE_Format_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_values::Inl
                { v: rest2 }
            }
        };
    let mut sigbuf: [u8; 64] = [0u8; 64usize];
    let sigbuf2: &mut [u8] = &mut sigbuf;
    create_sig(privkey, phdr, aad, payload, sigbuf2);
    let outbuf_sz: usize =
        crate::coseformat::serialize_cose_sign1_tagged(
            crate::coseformat::cose_sign1
            {
                protected: phdr,
                unprotected: uhdr,
                payload:
                crate::coseformat::either__COSE_Format_bstr_COSE_Format_nil::Inl { v: payload },
                signature: sigbuf2
            },
            outbuf
        );
    if outbuf_sz == 0usize
    {
        crate::commonabort::abort();
        outbuf
    }
    else
    {
        let res: &[u8] = &outbuf[0usize..outbuf_sz];
        res
    }
}

pub fn sign1_simple <'a>(privkey: &'a [u8], payload: &'a [u8], outbuf: &'a mut [u8]) ->
    &'a [u8]
{
    let uhdrauxbuf: [(crate::coseformat::evercddl_label, crate::cbordetveraux::cbor_raw); 0] =
        [dummy_map_val(); 0usize];
    let rest2: &[(crate::coseformat::evercddl_label, crate::cbordetveraux::cbor_raw)] =
        &uhdrauxbuf;
    let uhdr: crate::coseformat::header_map =
        crate::coseformat::header_map
        {
            intkey1: crate::coseformat::option__COSE_Format_evercddl_label_ugly::None,
            intkey2:
            crate::coseformat::option__FStar_Pervasives_either__CDDL_Pulse_Types_slice__COSE_Format_aux_env34_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env34_type_1::None,
            intkey3: crate::coseformat::option__COSE_Format_aux_env29_type_1_ugly::None,
            intkey4: crate::coseformat::option__COSE_Format_bstr::None,
            _x0:
            crate::coseformat::either__·COSE_Format_bstr···FStar_Pervasives_Native_option__COSE_Format_everparsenomatch·_FStar_Pervasives_either__·COSE_Format_bstr···FStar_Pervasives_Native_option__COSE_Format_everparsenomatch·_·FStar_Pervasives_Native_option__COSE_Format_everparsenomatch···FStar_Pervasives_Native_option__COSE_Format_everparsenomatch·::Inr
            {
                v:
                crate::coseformat::either__·COSE_Format_bstr···FStar_Pervasives_Native_option__COSE_Format_everparsenomatch·_·FStar_Pervasives_Native_option__COSE_Format_everparsenomatch···FStar_Pervasives_Native_option__COSE_Format_everparsenomatch·::Inr
                {
                    v:
                    (
                        crate::coseformat::option__COSE_Format_everparsenomatch::None,crate::coseformat::option__COSE_Format_everparsenomatch::None
                    )
                }
            },
            _x1:
            crate::coseformat::either__CDDL_Pulse_Types_slice__·COSE_Format_evercddl_label···COSE_Format_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_values::Inl
            { v: rest2 }
        };
    let aadbuf: [u8; 0] = [0u8; 0usize];
    let aadslice: &[u8] = &aadbuf;
    let alg: i32 = -8i32;
    let phdrauxbuf: [(crate::coseformat::evercddl_label, crate::cbordetveraux::cbor_raw); 0] =
        [dummy_map_val(); 0usize];
    let alg·: crate::coseformat::evercddl_int = mk_int(alg);
    let rest20: &[(crate::coseformat::evercddl_label, crate::cbordetveraux::cbor_raw)] =
        &phdrauxbuf;
    let phdr: crate::coseformat::empty_or_serialized_map =
        crate::coseformat::empty_or_serialized_map::Mkempty_or_serialized_map0
        {
            _x0:
            crate::coseformat::header_map
            {
                intkey1:
                crate::coseformat::option__COSE_Format_evercddl_label_ugly::Some
                { v: crate::coseformat::evercddl_label_ugly::Inl { v: alg· } },
                intkey2:
                crate::coseformat::option__FStar_Pervasives_either__CDDL_Pulse_Types_slice__COSE_Format_aux_env34_type_1_CDDL_Pulse_Parse_ArrayGroup_array_iterator_t__CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw_COSE_Format_aux_env34_type_1::None,
                intkey3: crate::coseformat::option__COSE_Format_aux_env29_type_1_ugly::None,
                intkey4: crate::coseformat::option__COSE_Format_bstr::None,
                _x0:
                crate::coseformat::either__·COSE_Format_bstr···FStar_Pervasives_Native_option__COSE_Format_everparsenomatch·_FStar_Pervasives_either__·COSE_Format_bstr···FStar_Pervasives_Native_option__COSE_Format_everparsenomatch·_·FStar_Pervasives_Native_option__COSE_Format_everparsenomatch···FStar_Pervasives_Native_option__COSE_Format_everparsenomatch·::Inr
                {
                    v:
                    crate::coseformat::either__·COSE_Format_bstr···FStar_Pervasives_Native_option__COSE_Format_everparsenomatch·_·FStar_Pervasives_Native_option__COSE_Format_everparsenomatch···FStar_Pervasives_Native_option__COSE_Format_everparsenomatch·::Inr
                    {
                        v:
                        (
                            crate::coseformat::option__COSE_Format_everparsenomatch::None,crate::coseformat::option__COSE_Format_everparsenomatch::None
                        )
                    }
                },
                _x1:
                crate::coseformat::either__CDDL_Pulse_Types_slice__·COSE_Format_evercddl_label···COSE_Format_values·_CDDL_Pulse_Parse_MapGroup_map_iterator_t__CBOR_Pulse_Raw_Type_cbor_raw_CBOR_Pulse_Raw_Type_cbor_map_entry_CBOR_Pulse_Raw_Iterator_cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_map_entry_COSE_Format_evercddl_label_COSE_Format_values::Inl
                { v: rest20 }
            }
        };
    let mut sigbuf: [u8; 64] = [0u8; 64usize];
    let sigbuf2: &mut [u8] = &mut sigbuf;
    create_sig(privkey, phdr, aadslice, payload, sigbuf2);
    let outbuf_sz: usize =
        crate::coseformat::serialize_cose_sign1_tagged(
            crate::coseformat::cose_sign1
            {
                protected: phdr,
                unprotected: uhdr,
                payload:
                crate::coseformat::either__COSE_Format_bstr_COSE_Format_nil::Inl { v: payload },
                signature: sigbuf2
            },
            outbuf
        );
    if outbuf_sz == 0usize
    {
        crate::commonabort::abort();
        outbuf
    }
    else
    {
        let res: &[u8] = &outbuf[0usize..outbuf_sz];
        res
    }
}

pub fn verify_sig(
    pubkey: &[u8],
    phdr: crate::coseformat::empty_or_serialized_map,
    aad: &[u8],
    payload: &[u8],
    sigbuf: &[u8]
) ->
    bool
{
    let sz: usize = 1024usize;
    let mut arr: Box<[u8]> = vec![0u8; sz].into_boxed_slice();
    let outbuf: &mut [u8] = &mut arr;
    let sig_struct: crate::coseformat::sig_structure =
        crate::coseformat::sig_structure
        {
            context: crate::coseformat::evercddl_int_ugly_tags::Inr,
            body_protected: phdr,
            _x0:
            crate::coseformat::either__·COSE_Format_empty_or_serialized_map····COSE_Format_bstr···COSE_Format_bstr··_·COSE_Format_bstr···COSE_Format_bstr·::Inr
            { v: (aad,payload) }
        };
    let written: usize = crate::coseformat::serialize_sig_structure(sig_struct, outbuf);
    if written == 0usize
    {
        crate::commonabort::abort();
        false
    }
    else
    {
        let res: &[u8] = &outbuf[0usize..written];
        let tbs: &[u8] = res;
        let success: bool = crate::ed25519::verify(pubkey, tbs, sigbuf);
        success
    }
}

pub type good_signature = ();

fn uu___is_Inl__COSE_Format_bstr_COSE_Format_nil(
    projectee: crate::coseformat::either__COSE_Format_bstr_COSE_Format_nil
) ->
    bool
{
    match projectee
    { crate::coseformat::either__COSE_Format_bstr_COSE_Format_nil::Inl { .. } => true, _ => false }
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
    crate::coseformat::option__·COSE_Format_cose_sign1_tagged···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::coseformat::validate_and_parse_cose_sign1_tagged(msg);
    match res
    {
        crate::coseformat::option__·COSE_Format_cose_sign1_tagged···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__Pulse_Lib_Slice_slice·uint8_t::None,
        crate::coseformat::option__·COSE_Format_cose_sign1_tagged···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: res1 }
        =>
          {
              let x: crate::coseformat::cose_sign1 = res1.0;
              let rem: &[u8] = res1.1;
              if rem.len() == 0usize && uu___is_Inl__COSE_Format_bstr_COSE_Format_nil(x.payload)
              {
                  let sig: &[u8] = x.signature;
                  let success: bool =
                      if sig.len() == 64usize
                      {
                          verify_sig(
                              pubkey,
                              x.protected,
                              aad,
                              match x.payload
                              {
                                  crate::coseformat::either__COSE_Format_bstr_COSE_Format_nil::Inl
                                  { v }
                                  => v,
                                  _ => panic!("Incomplete pattern matching")
                              },
                              sig
                          )
                      }
                      else
                      { false };
                  if success
                  {
                      let payload: &[u8] =
                          match x.payload
                          {
                              crate::coseformat::either__COSE_Format_bstr_COSE_Format_nil::Inl
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
    crate::coseformat::option__·COSE_Format_cose_sign1_tagged···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::coseformat::validate_and_parse_cose_sign1_tagged(msg);
    match res
    {
        crate::coseformat::option__·COSE_Format_cose_sign1_tagged···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__Pulse_Lib_Slice_slice·uint8_t::None,
        crate::coseformat::option__·COSE_Format_cose_sign1_tagged···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: res1 }
        =>
          {
              let x: crate::coseformat::cose_sign1 = res1.0;
              let rem: &[u8] = res1.1;
              if rem.len() == 0usize && uu___is_Inl__COSE_Format_bstr_COSE_Format_nil(x.payload)
              {
                  let sig: &[u8] = x.signature;
                  let success: bool =
                      if sig.len() == 64usize
                      {
                          verify_sig(
                              pubkey,
                              x.protected,
                              aadslice,
                              match x.payload
                              {
                                  crate::coseformat::either__COSE_Format_bstr_COSE_Format_nil::Inl
                                  { v }
                                  => v,
                                  _ => panic!("Incomplete pattern matching")
                              },
                              sig
                          )
                      }
                      else
                      { false };
                  if success
                  {
                      let payload: &[u8] =
                          match x.payload
                          {
                              crate::coseformat::either__COSE_Format_bstr_COSE_Format_nil::Inl
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
