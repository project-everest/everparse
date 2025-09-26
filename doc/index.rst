.. The EverParse user manual documentation master file
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

Verified efficient parsing for binary data formats
==================================================

EverParse is a framework for generating verified secure parsers and
formatters from domain-specific format specification languages.

The framework contains several components:

**LowParse**: At the core of EverParse is *LowParse*, a verified library
of parsing and formatting combinators programmed and verified in F\*.

**3D**: A frontend for EverParse to enable specifying data
formats in an style resembling type definitions in the C programming
language. We have used it to generate message validation code for use
within several low-level C programs.

**QuackyDucky**: A frontend for EverParse that accepts data formats
in a style common to many RFCs. We have used it to generate message
processing code for several networking protocols, including TLS and
QUIC.

**EverCBOR**: A verified C and Rust library for CBOR parsing and
serialization. Currently, EverCBOR supports the deterministic encoding
(RFC 8949 Section 4.2) without floating-point numbers; supporting the
full CBOR is work in progress.

**EverCDDL**: An experimental frontend for EverParse that accepts data
formats for CBOR objects in CDDL, and generates C or Rust data types,
parsers and serializers. We have used it to generate message
processing code for COSE signing.

EverParse is open-source and available on `GitHub
<https://github.com/project-everest/everparse/>`_. EverParse is part
of `Project Everest <https://project-everest.github.io/>`_.

Releases
--------

We produce public releases under the form of a Windows or Linux
standalone binary (x86_64) package and a platform-independent source
package.

The latest release of EverParse can be found `here <https://github.com/project-everest/everparse/releases>`_.

Those public releases do not contain EverCBOR/EverCDDL. By contrast,
we produce `pre-built Docker images containing only EverCBOR and EverCDDL <https://github.com/project-everest/everparse/pkgs/container/evercbor>`_

Manual
------

* :ref:`3d` (includes the full documentation of the EverParse binary package)

* :ref:`build`

* EverCBOR:

  + `Documented C example <https://github.com/project-everest/everparse/blob/master/src/cbor/pulse/det/c/example/main.c>`_

  + `Rust API reference <https://project-everest.github.io/everparse/evercbor-rust/cborrs/>`_
  
In the News
-----------
`EverParse: Hardening critical attack surfaces with formally proven message parsers <https://www.microsoft.com/en-us/research/blog/everparse-hardening-critical-attack-surfaces-with-formally-proven-message-parsers/>`_;
  Tahina Ramananandro, Aseem Rastogi and Nikhil Swamy;
  Microsoft Research blog

Papers
------

`Secure Parsing and Serializing with Separation Logic Applied to CBOR, CDDL and COSE <https://arxiv.org/abs/2505.17335>`_;
  Tahina Ramananandro, Gabriel Ebner, Guido Martinez, Nikhil Swamy;

  32nd ACM SIGSAC Conference on Computer and Communications Security (CCS), 2025 (accepted for publication, to appear)

`ASN1*: Provably Correct Non-Malleable Parsing for ASN.1 DER <https://www.microsoft.com/en-us/research/publication/asn1-provably-correct-non-malleable-parsing-for-asn-1-der/>`_;
  Haobin Ni, Antoine Delignat-Lavaud, Cédric Fournet, Tahina Ramananandro, Nikhil Swamy;

  In Proceedings of the ACM SIGPLAN international conference on Certified Programs and Proofs (CPP), 2022

`Hardening Attack Surfaces with Formally Proven Binary Format Parsers <https://www.microsoft.com/en-us/research/publication/hardening-attack-surfaces-with-formally-proven-binary-format-parsers/>`_;
  Nikhil Swamy, Tahina Ramananandro, Aseem Rastogi, Irina Spiridonova, Haobin Ni, Dmitry Malloy, Juan Vazquez, Michael Tang, Omar Cardona, Arti Gupta;

  In Proceedings of the 43rd ACM SIGPLAN International Conference on Programming Language Design and Implementation, 2022

`DICE*: A Formally Verified Implementation of DICE Measured Boot <https://www.microsoft.com/en-us/research/publication/dice-a-formally-verified-implementation-of-dice-measured-boot/>`_;
  Zhe Tao, Aseem Rastogi, Naman Gupta, Kapil Vaswani and Aditya V. Thakur;

  In Proceedings of the 30th USENIX Security Symposium, 2021

`A Security Model and Fully Verified Implementation for the IETF QUIC Record Layer <https://project-everest.github.io/assets/everquic.pdf>`_;
  Antoine Delignat-Lavaud, Cedric Fournet, Bryan Parno, Jonathan Protzenko, Tahina Ramananandro, Jay Bosamiya, Joseph Lallemand, Itsaka Rakotonirina, and Yi Zhou;

  In Proceedings of the 42nd IEEE Symposium on Security and Privacy, 2021

`EverParse: Verified Secure Zero-Copy Parsers for Authenticated Message Formats <https://project-everest.github.io/assets/everparse.pdf>`_;
  Tahina Ramananandro, Antoine Delignat-Lavaud, Cedric Fournet, Nikhil Swamy, Tej Chajed, Nadim Kobeissi, and Jonathan Protzenko;

  In Proceedings of the 28th USENIX Security Symposium, 2019

.. toctree::
   :hidden:
   :maxdepth: 1
   :caption: Contents:

   3d
   build


Licenses
========

EverParse is Copyright 2018, 2019, 2020, 2021 Microsoft Corporation. All
rights reserved. EverParse is free software, licensed by Microsoft
Corporation under the `Apache License 2.0
<https://github.com/project-everest/everparse/blob/master/LICENSE>`_.

Additionally, the licenses of all dependencies included in the
EverParse binary packages (F\*, KaRaMeL, z3, EverCrypt, clang-format) are all
stored in the ``licenses/`` subdirectory of the EverParse binary
package once extracted.


Indices and tables
==================

* :ref:`genindex`
* :ref:`search`
