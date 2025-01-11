.. _build:

How to build EverParse from source
==================================

You may want to use the sources instead of the binary package in any
of the following cases:

* You are on a non-x86_64 platform (however, there is no guarantee that
  the sources will compile under any such non-x86_64 platform.)

* You are not on Windows or Linux (however, there is no guarantee that
  the sources will compile under any such non-Windows-Linux system.)

* You want to use your own copy of F\*, KaRaMeL or z3.

* You want to contribute to EverParse.

To this end, you must first install dependencies, then compile the
sources.

Install dependencies
--------------------

EverParse, F\* and KaRaMeL are all components of the Everest
project. Thus, the best way to install dependencies is to use the
Everest script, as described below following the `website of the
Everest project <https://project-everest.github.io/>`_, which
EverParse is a member of.

Windows
^^^^^^^

Building EverParse on Windows requires Cygwin. Instead, you could also
use the `Windows Subsystem for Linux (WSL)
<https://docs.microsoft.com/en-us/windows/wsl/install-win10>`_ and act
as if you were on Linux (see below), but this has not been officially
tested by anyone in the Everest project; you will obtain Linux
binaries instead.


1. `Install Cygwin <https://www.cygwin.com/>`_.

2. Clone the `Everest repository from GitHub
   <https://github.com/project-everest/everest>`_.

3. From inside the origin directory of the clone, run ``./everest
   check`` and follow the instructions on how to install compilation
   dependencies (OCaml, etc.) ``./everest check`` will automatically
   install all such compilation dependencies, but you may need to
   re-run it several times after refreshing the environment.

Linux
^^^^^

1. `Install opam <https://opam.ocaml.org/doc/Install.html>`_, a
   package manager for the `OCaml
   <https://ocaml.org/doc/Install.html>`_ ecosystem.

   .. note::

      You need to install opam 2.x, so beware of older distributions
      such as Ubuntu 18.04 packaging opam 1.x by default. The opam web
      page gives detailed installation instructions to install opam
      2.x.

2. Make sure the system packages corresponding to the following
   commands are installed:

   * GNU cp
   * GNU date
   * diff
   * find
   * gcc
   * GNU getopt
   * git
   * GNU make
   * patch
   * GNU sed
   * wget
   * which

3. Run ``opam init --compiler=4.14.0`` and follow the instructions. This will install OCaml.

   This step will modify your configuration scripts to add the path to
   OCaml and its libraries to the PATH environment variable every time
   you login, so you may need to evaluate those configuration scripts
   again or log out and back in for such changes to take effect.

   .. note::

      You need to specify an OCaml version number (between 4.12.0 and
      4.14.x), so that OCaml will be installed in your user profile,
      because some EverParse dependencies do not work well with a
      system-wide OCaml. Thus, if opam says that there is an
      ambiguity, you should re-run ``opam init`` with the non-system
      package for OCaml.

   If this step fails, then you will need to remove the ``~/.opam``
   directory before trying again.

4. Clone the `Everest repository from GitHub
   <https://github.com/project-everest/everest>`_.

5. From inside the origin directory of the clone, run ``./everest
   opam`` and follow the instructions. This step will install the
   relevant opam packages on which EverParse depends.



Compile the sources
-------------------

There are two possible ways.

* If your platform is not supported (or if binary releases do not work
  for some reason) and if you just want to rebuild EverParse, then you
  can build a binary package.

* If you want to contribute to the EverParse sources, then you need to
  build in the source tree.

Build a binary package
^^^^^^^^^^^^^^^^^^^^^^

If you just want to rebuild EverParse without contributing to its
sources, you can build a binary package:

1. `Clone the EverParse repository <https://github.com/project-everest/everparse>`_ .

2. In the root directory of that EverParse clone, run one of the following commands:

   * ``make everparse``

     That command will build ready-to-use binaries into the
     ``everparse/`` subdirectory. That directory will behave as if you
     had downloaded and extracted a binary package archive from the
     releases page.

     This process is fully automatic. In particular, it automatically
     downloads a binary release of z3, and downloads and builds F\*,
     and KaRaMeL.

     .. note::

        z3 is downloaded only for Windows or Linux. On other platforms, you need to have Z3 4.8.5
        reachable from your PATH. You will most likely need to compile it from `its sources <https://github.com/z3prover/z3/tree/Z3-4.8.5>`_.


   * ``make package``

     That command will build a binary package,
     ``everparse-<version>-<platform>.zip`` on Windows, ``.tar.gz`` on
     Linux, by producing the ``everparse/`` subdirectory as with
     ``make everparse`` and compressing it into an archive.


   * ``make package-noversion``

     That command will build a binary package, as with ``make
     package``, but only the name of the archive will change:
     ``everparse.zip`` on Windows, ``everparse.tar.gz`` on Linux.

In all cases, the produced package offers ``everparse.cmd`` on
Windows, ``everparse.sh`` on Linux, which you can use as directed
elsewhere in this manual.

Build in the source tree
^^^^^^^^^^^^^^^^^^^^^^^^

If you want to contribute to the sources of EverParse, you need to
rebuild in the source tree. To do so, you first need to setup a
development environment for Everest (steps 1 to 6 below). Then you can
fetch and build EverParse sources:

.. note::

   You cannot use ``everparse.sh`` or ``everparse.cmd`` from the
   source tree. You need to use ``bin/3d.exe`` instead.


1. In the root directory of the Everest clone, run ``./everest z3``
   and follow the instructions to install z3 on your system.

   This step will modify your configuration scripts to add the path to
   z3 to the PATH environment variable every time you login, so you
   may need to evaluate those configuration scripts again or log out
   and back in for such changes to take effect.

   .. note::

      z3 is downloaded only for Windows or Linux. On other platforms, you need to have Z3 4.8.5
      reachable from your PATH. You will most likely need to compile it from `its sources <https://github.com/z3prover/z3/tree/Z3-4.8.5>`_.


2. Run ``./everest pull`` to fetch and pull the latest versions of F\*,
   KaRaMeL and EverParse.

3. Run ``./everest -j 1 FStar make karamel make`` to
   build F\* and KaRaMeL. The ``-j`` option introduces a
   parallelism factor. You can also speed up the build by skipping
   F\* and KaRaMeL library proofs by setting the
   ``OTHERFLAGS`` environment variable to ``"--admit_smt_queries
   true"``.

   .. note::

      If, at this point, you immediately get an error of the form
      "menhir not found", then it means that the path to opam packages
      is not properly set up in your environment. To do so, you need
      to run ``eval $(opam env)`` (as instructed during ``opam init``
      or ``./everest opam``), or log out and back in.

4. Install F*, and make sure ``fstar.exe`` is your PATH. As an alternative,
   define the environment variable ``FSTAR_EXE`` to the full path of
   the ``fstar.exe`` executable.

5. Set the ``KRML_HOME`` environment variable to the ``karamel``
   subdirectory of your Everest clone, which contains a clone of the
   latest KaRaMeL.

   .. note::
      
      If you already have your own copy of F\* or KaRaMeL, and if you
      already know how to build them, then you can skip steps 1 to 5
      and set the environment variables accordingly.)

6. Everest contains a clone of the EverParse sources in the
   ``quackyducky`` subdirectory. You can work from
   there. Alternatively, you can `clone it yourself
   <https://github.com/project-everest/everparse>`_
   anywhere else.

7. Set the ``EVERPARSE_HOME`` environment variable to your EverParse clone
   as you chose it.

8. Then, once you are all set up in your EverParse clone, you can
   build EverParse by ``make``. Then, the EverParse/3d executable will
   be located at ``bin/3d.exe``.

