/*++

Copyright (c) Microsoft Corporation

Module Name:

EverParseError.h

Abstract:

This is an EverParse-generated file to hook a user-defined error
reporting function to EverParse-generated validators.

Authors:

nswamy, protz, taramana 5-Feb-2020

--*/
#ifndef __EverParseError_H
#define ___EverParseError_H
static char* EverParseErrorReasonOfResult (uint64_t code)
{
    switch (EverParseErrorKindOfResult(code)) {
        case 1: return "generic error";
        case 2: return "not enough data";
        case 3: return "impossible";
        case 4: return "list size not multiple of element size";
        case 5: return "action failed";
        case 6: return "constraint failed";
        default: return "unspecified";
    }
}
#endif
