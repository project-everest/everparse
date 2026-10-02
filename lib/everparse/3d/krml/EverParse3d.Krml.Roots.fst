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

(* For CUSTARD_ENTRIES; see extract.Makefile. *)
module PulsePervasives = Pulse.Lib.Pervasives
