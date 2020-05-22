.. The EverParse user manual documentation master file
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

Verified efficient parsing for binary data formats
==================================================

EverParse is a framework for generating verified secure parsers and
formatters from domain-specific format specification languages.

The framework contains three components:

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


Releases
--------

We produce public releases under the form of a Windows standalone
binary package and a platform-independent source package.

The latest release of EverParse can be found `here <https://github.com/project-everest/everparse/releases>`_.

Manual
------

* :ref:`3d` (includes the full documentation of the EverParse Windows binary package)


Papers
------

`EverParse: Verified Secure Zero-Copy Parsers for Authenticated Message Formats <https://project-everest.github.io/assets/everparse.pdf>`_;
  Tahina Ramananandro, Antoine Delignat-Lavaud, Cedric Fournet, Nikhil Swamy, Tej Chajed, Nadim Kobeissi, and Jonathan Protzenko;
  In Proceedings of the 28th USENIX Security Symposium, 2019

.. toctree::
   :hidden:
   :maxdepth: 1
   :caption: Contents:

   3d


Indices and tables
==================

* :ref:`genindex`
* :ref:`search`
