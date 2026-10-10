(* The single file named on Custard's command line for the Pulse 3d runtime.

   Custard loads the whole program from the dependency closure of the root
   file, and `-o' allows exactly one root. The runtime has no single top
   module -- the three input stream backends are siblings, and each one's
   error handler is a leaf above EverParse3d.Actions.Base -- so this module
   names them all and nothing else.

   It declares no definitions, so it contributes nothing to the extracted
   .krml; what is actually rooted is CUSTARD_ENTRY_MODULES in extract.Makefile.
   The module abbreviations exist only to put each module in the closure. *)
module EverParse3d.Krml.Roots

module ActionsBase = EverParse3d.Actions.Base
module ActionsCommon = EverParse3d.Actions.Common
module ErrorHandlerBuffer = EverParse3d.Actions.ErrorHandler.Buffer
module ErrorHandlerExtern = EverParse3d.Actions.ErrorHandler.Extern
module AppCtxt = EverParse3d.AppCtxt
module CopyBuffer = EverParse3d.CopyBuffer
module CopyBufferBuffer = EverParse3d.CopyBuffer.Buffer
module ErrorCode = EverParse3d.ErrorCode
module InputStreamBase = EverParse3d.InputStream.Base
module InputStreamBuffer = EverParse3d.InputStream.Buffer
module InputStreamBufferTypes = EverParse3d.InputStream.Buffer.Types
module InputStreamExtern = EverParse3d.InputStream.Extern
module InputStreamExternNullPtr = EverParse3d.InputStream.Extern.NullPtr
module InputStreamExternTypes = EverParse3d.InputStream.Extern.Types
module InputStreamStatic = EverParse3d.InputStream.Static
module Kinds = EverParse3d.Kinds
module Prelude = EverParse3d.Prelude
module PreludeStaticHeader = EverParse3d.Prelude.StaticHeader
module ProbeActions = EverParse3d.ProbeActions
module State = EverParse3d.State

(* The `--api lowstar` runtime; see CUSTARD_ENTRY_MODULES in extract.Makefile. *)
module ErrorHandlerLowstarBuffer = EverParse3d.Actions.ErrorHandler.LowstarBuffer
module ErrorHandlerLowstarExtern = EverParse3d.Actions.ErrorHandler.LowstarExtern
module CopyBufferLowstarBuffer = EverParse3d.CopyBuffer.LowstarBuffer
module CopyBufferLowstarExtern = EverParse3d.CopyBuffer.LowstarExtern
module InputStreamLowstarBuffer = EverParse3d.InputStream.LowstarBuffer
module InputStreamLowstarExtern = EverParse3d.InputStream.LowstarExtern
module InputStreamLowstarExternRaw = EverParse3d.InputStream.LowstarExtern.Raw
module InputStreamLowstarExternTypes = EverParse3d.InputStream.LowstarExtern.Types
module LowstarBufferAdapter = EverParse3d.Lowstar.BufferAdapter
module LowstarErrorCode = EverParse3d.Lowstar.ErrorCode
module LowstarExternAdapter = EverParse3d.Lowstar.ExternAdapter
module LowstarExternAdapterSpec = EverParse3d.Lowstar.ExternAdapter.Spec
module LowstarPublic = EverParse3d.Lowstar.Public
module LowstarSupportBuffer = EverParse3d.Lowstar.SupportBuffer
module LowstarSupportExtern = EverParse3d.Lowstar.SupportExtern

(* For CUSTARD_ENTRIES; see extract.Makefile. *)
module PulsePervasives = Pulse.Lib.Pervasives
