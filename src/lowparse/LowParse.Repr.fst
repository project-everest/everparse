(*
  Copyright 2015--2019 INRIA and Microsoft Corporation

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.

  Authors: T. Ramananandro, A. Rastogi, N. Swamy, A. Fromherz
*)
module LowParse.Repr

module LP = LowParse.Low.Base
module LS = LowParse.SLow.Base
module B = LowStar.Buffer
module HS = FStar.HyperStack
module C = LowStar.ConstBuffer
module U32 = FStar.UInt32
module U64 = FStar.UInt64

open FStar.Integers
open FStar.HyperStack.ST

module ST = FStar.HyperStack.ST
module I = LowStar.ImmutableBuffer

let valid (#t:Type) (p:repr_ptr t) (h:HS.mem)
  = valid' p h

let reveal_valid ()
  : Lemma (forall (t:Type) (p:repr_ptr t) (h:HS.mem).
              {:pattern (valid #t p h)}
           valid #t p h <==> valid' #t p h)
  = ()

let frame_valid #t (p:repr_ptr t) (l:B.loc) (h0 h1:HS.mem)
  : Lemma
    (requires
      valid p h0 /\
      B.modifies l h0 h1 /\
      B.loc_disjoint (fp p) l)
    (ensures
      valid p h1)
    [SMTPat (valid p h1);
     SMTPat (B.modifies l h0 h1)]
  = ()
