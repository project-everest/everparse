#!/usr/bin/env bash

# This script installs EverParse build dependencies (including OCaml,
# but not Cygwin, which is already required on Windows to run this
# script.)  It is inspired from project-everest/everest

# Sorry, everyone
if (( ${BASH_VERSION%%.*} < 4 )); then
  echo "This script requires Bash >= 4. On OSX, try: brew install bash"
  exit 1
fi

# Any error is fatal.
set -e
set -o pipefail
# set -x # uncomment for debugging.
# set -u

# Known URLs, directories and versions
OPAM_URL=https://github.com/fdopen/opam-repository-mingw/releases/download/0.0.0.2/opam64.tar.xz
MINIMAL_OCAML_VERSION=4.14.0
OPAM_VERSION=4.14.0+mingw64c
SED=$(which gsed >/dev/null 2>&1 && echo gsed || echo sed)
MAKE=$(which gmake >/dev/null 2>&1 && echo gmake || echo make)

# OPAM_AUTO_SETUP defines the opam command-line option to
# automatically setup environment variables into
# $EVEREST_ENV_DEST_FILE . By default, it is left empty, but it is set
# to --auto-setup if everest is run with --yes, i.e. in
# non-interactive mode
OPAM_AUTO_SETUP=

ADVANCE_YES=false

# No-interaction when this script is used for CI purposes
INTERACTIVE=true
make_non_interactive () {
  INTERACTIVE=false
  export GIT_SSH_COMMAND="ssh -oBatchMode=yes"
  export GIT_TERMINAL_PROMPT=0
  export OPAMYES=1
  export NOSHORTLOG=1
  export ADVANCE_YES=true
  OPAM_AUTO_SETUP=--auto-setup
}

# The parallel option, either empty (by default), or -j n,
# as specified on the command line.
# WARNING: in the latter case, it MUST be interpreted as two words, so
# NEVER quote it as "$parallel_opt"
# Use $parallel_opt instead
unset parallel_opt

# The -k option (to instruct make to keep going upon a failure),
# disabled by default
unset keep_going_opt

# A string made of both options above, for convenience
unset make_opts

set_make_opts () {
  make_opts="$parallel_opt $keep_going_opt"
}

# The file where to store customized environment variables
if [[ $EVEREST_ENV_DEST_FILE == "" ]] ; then
  # For people who have installed and initialized opam prior to
  # running ./everest check, opam will modify .profile instead of
  # .bash_profile, if the latter does not exist. So we need to
  # account for that case.
  if [[ -f "$HOME/.bash_profile" ]] ; then
      EVEREST_ENV_DEST_FILE="$HOME/.bash_profile"
  else
      EVEREST_ENV_DEST_FILE="$HOME/.profile"
  fi
fi

# cd to the script directory
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"

# "Modularity": include other files (requires us to be in the right directory)
source lib.sh

GETOPT=getopt
if is_osx; then
  export PATH=$(brew --prefix gnu-getopt)/bin:$PATH
  echo $PATH
fi

# -allow a command to fail with !’s side effect on errexit
# -use return value from ${PIPESTATUS[0]}, because ! hosed $?
! $GETOPT --test > /dev/null
if [[ ${PIPESTATUS[0]} -ne 4 ]]; then
  echo "you have an antiquated getopt; on Mac OS X, run \"brew install gnu-getopt\" and make sure it comes first in the PATH"
  exit 1
fi

# ------------------------------------------------------------------------------
# A series of helpers
# ------------------------------------------------------------------------------

write_to_env_dest_file () {
  str="$1"
  # NOTE: "$str" contains line breaks, since it actually contains
  # several commands, with each command on its own line.
  # These line breaks must be preserved.
  eval "$str"
  echo "$str" >> "$EVEREST_ENV_DEST_FILE"
  magenta "Remember to run source \"$EVEREST_ENV_DEST_FILE\" in your terminal afterwards!"
}

write_z3_env_dest_file () {
  str="
    # This line automatically added by $0
    export PATH=$(pwd)/$1/bin:\$PATH"
  write_to_env_dest_file "$str"
}

write_cygwin_env_dest_file () {
  str="
    # These lines automatically added by $0
    export PATH=/usr/x86_64-w64-mingw32/sys-root/mingw/bin:\$PATH
    export CYGWIN='winsymlinks:native'"
  write_to_env_dest_file "$str"
}

write_cxx_env_dest_file () {
  str="
    # This line automatically added by $0
    export CXX=x86_64-w64-mingw32-g++.exe"
  write_to_env_dest_file "$str"
}

write_everest_env_dest_file () {
  if is_windows; then
    str="
    # These lines automatically added by $0
    export EVEREST_SCONS_CACHE_DIR=$(cygpath -m \"$TEMP\"/everest)"
  else
    str="
    # These lines automatically added by $0
    export EVEREST_SCONS_CACHE_DIR=/tmp/everest"
  fi
  write_to_env_dest_file "$str"
}

write_gh_env_dest_file () {
  str="
    # This line automatically added by $0
    export PATH=$(pwd)/gh/bin:\$PATH"
  write_to_env_dest_file "$str"
}

cygsetup="setup-x86_64.exe"
cygsetup_args="--no-desktop --no-shortcuts --no-startmenu --wait --quiet-mode"
# Find Cygwin's setup utility, or download it from the internet.
# Success: writes the path to Cygwin's setup in $cygsetup
# Failure: aborts.
find_cygsetup () {
  found=false
  for s in "$USERPROFILE/Desktop/setup-x86_64.exe" "$USERPROFILE/Downloads/setup-x86_64.exe" "./setup-x86_64.exe" "c:/cygwin64/setup-x86_64.exe"; do
    if [ -x "$s" ]; then
      echo "Found $cygsetup"
      found=true
      cygsetup="$s"
    fi
  done

  # Try to find chocolatey version
  if ! $found; then
    for s in "$USERPROFILE/Desktop/cygwinsetup.exe" "$USERPROFILE/Downloads/cygwinsetup.exe" "./cygwinsetup.exe" "c:/cygwin64/cygwinsetup.exe"; do
     if [ -x "$s" ]; then
       echo "Found $cygsetup"
       found=true
       cygsetup="$s"
      fi
    done
  fi

  if ! $found; then
    magenta "Cygwin setup not found, downloading it"
    if ! command -v wget >/dev/null 2>&1; then
      red "ERROR: please either place cygwin's setup-x86_64.exe in your Downloads or Desktop folder, or install wget via cygwin's setup"
    fi
    wget "https://cygwin.com/setup-x86_64.exe"
    chmod a+x setup-x86_64.exe
    cygsetup=./setup-x86_64.exe
  fi
}

install_all_opam_packages () {
  packages=$(cat opam-packages | cut -d ' ' -f 2 | tr '\n' ' ')
  opam update
  if is_windows; then
    opam install depext-cygwinports
  else
    opam depext $packages
  fi
  opam install -j 4 $packages
}

try_git_clone () {
  if ! git clone --recursive $1 $3; then
    magenta "Proceed with https? [Yn]"
    prompt_yes true "exit 1"
    git clone --recursive $2 $3
  fi
}

parse_z3_version () {
  if ! which z3 >/dev/null 2>&1; then
    echo "no z3 in path!"
  else
    local z3_version=$(z3 --version)
    if echo $z3_version | grep hashcode >/dev/null 2>&1; then
      z3 --version | $SED 's/.*build hashcode \(.*\)/\1/' | tr -d '\r'
    else
      z3 --version | $SED 's/Z3 version \([0-9\.]\+\).*/\1/'
    fi
  fi
}

# ------------------------------------------------------------------------------
# The functions that implement the main actions
# ------------------------------------------------------------------------------

use_our_z3 () {
    local z3_dir=$(realpath $PWD)/z3
    if ! PATH="$z3_dir/bin:$PATH" which z3 >/dev/null 2>&1 ; then
        red "Z3 has not been compiled yet, abort"
        exit 1
    fi
    magenta "Automatically customize $EVEREST_ENV_DEST_FILE with the z3 path? [Yn]"
    prompt_yes "write_z3_env_dest_file z3" true
}

no_z3=false

do_update_z3 () {
  if $no_z3 ; then
    echo "... skipping z3"
  else
    local current_z3=$(parse_z3_version)
    echo "... version of z3 found in PATH: $current_z3"
    local new_z3=4.13.3
    if [[ $new_z3 != $current_z3 ]]; then
        red "This is not z3 $current_z3"
        magenta "Use our existing z3? [Yn]"
        prompt_yes use_our_z3 false
    fi
  fi
}

do_check ()
{
  blue "Checking environment"

  # Basic utilities
  success_or "which" "please execute this script in a Unix environment"
  if is_osx; then
    local msg="please run \"brew install gnu-getopt coreutils gnu-sed findutils make\""
    brew --prefix gnu-getopt || echo $msg
    success_or "greadlink" "$msg"
    success_or "gsed" "$msg"
    success_or "gfind" "$msg"
    success_or "gmake" "$msg"
  fi

  # Slightly suboptimal, since we may end up running Cygwin's setup twice.
  if ! command -v git >/dev/null 2>&1; then
    if is_windows; then
      magenta "Git not found. Install Cygwin's git? [Yn]"
      find_cygsetup
      prompt_yes "$cygsetup $cygsetup_args --packages=git"
    else
      red "ERROR: git not found; install it via your favorite package manager"
      exit 1
    fi
  fi

  # Windows pre-requisites
  if is_windows; then
    # A list of known causes for failure
    if where.exe bash.exe | grep -v cygwin >/dev/null 2>&1; then
      red "ERROR: bash.exe has been found in a non-standard location!"
      echo "Please remove Bash for Windows and others (GNU for Windows, MSYS2, etc.)"
      red "Are you sure you want to continue? [Yn]"
      prompt_yes true "exit 1"
    else
      echo "... no suspicious bash"
    fi

    if [[ $(uname -m) != "x86_64" ]]; then
      red "ERROR: not a 64-bit Cygwin"
      echo "We've experienced tons of issues with 32-bit Cygwin. Time to upgrade."
      exit 1
    fi
    echo "... 64-bit cygwin"

    if cygwin_has "ocaml" || cygwin_has "flexdll"; then
      red "ERROR: please remove the cygwin ocaml and/or flexdll packages"
      exit 1
    fi
    echo "... no suspicious cygwin packages"

    if ! (flexlink.exe -help 2>&1 || true) | grep "fdopen" >/dev/null; then
        red "Warning: you have an unknown version of flexlink"
        red "Please use the version from https://fdopen.github.io/opam-repository-mingw/"
    else
        echo "... flexlink is good"
    fi

    # The list of required cygwin packages
    for p in $(cat cygwin-packages); do
      if ! cygwin_has $p; then
        find_cygsetup
        echo "Cygwin package $p is missing"
        if_yes "$cygsetup $cygsetup_args --packages=$(cat cygwin-packages | tr '\n' ,)"
      fi
    done
    echo "... all $(cat cygwin-packages | wc -l) cygwin packages seem to be installed"

    if ! command -v libsqlite3-0.dll >/dev/null 2>&1; then
      red "Warning: x86_64-mingw32 DLLs not in PATH"
      magenta "Automatically customize $EVEREST_ENV_DEST_FILE with the x86_64-mingw32 path + native windows symlinks?"
      prompt_yes write_cygwin_env_dest_file true
    else
      echo "... proper mingw directory seems to be in PATH"
    fi

    if [[ -z "$CXX" ]] ; then
      red "Warning: CXX not defined"
      magenta "Automatically set CXX to x86_64-w64-mingw32-g++.exe?"
      prompt_yes write_cxx_env_dest_file true
    fi
  fi # if is_windows

  # Note: ssh returns the exit code of the remote command (1 in this case),
  # hence the || true -- the success of this step is determined by the presence
  # of "authenticated".
  if ! (ssh -oStrictHostKeyChecking=no git@github.com 2>&1 || true) | grep authenticated >/dev/null; then
    magenta "Warning: git client not configured with the proper ssh credentials"
    echo "Hint: check which git you're running, and make sure you have the same SSH key in ~/.ssh and github.com"
  else
    echo "... github.com access ok"
  fi

  # OCaml detection
  if ! command -v >/dev/null 2>&1 ocaml; then
    # Offer to install and sed-setup a crappy snapshot
    if is_windows; then
      magenta "No OCaml detected!"
      cat <<MSG

Proceed with the download?
MSG
      prompt_yes true "exit 1"
      if [ -e ~/.opam ]; then
        red "Warning: stale ~/.opam; continue? [Yn]"
        prompt_yes true "exit 1"
      fi
      if [ -e /cygdrive/c/ocamlmgw64 ]; then
        red "Warning: stale /cygdrive/c/ocamlmgw64; continue? [Yn]"
        prompt_yes true "exit 1"
      fi
      # Download and Install OPAM
      wget $OPAM_URL
      tar -xf 'opam64.tar.xz'
      rm -f 'opam64.tar.xz'
      bash opam64/install.sh
      echo "Interactive is: $INTERACTIVE ; auto-setup is: $OPAM_AUTO_SETUP ; dot-profile is: $EVEREST_ENV_DEST_FILE ;"
      opam init default "https://github.com/fdopen/opam-repository-mingw.git#opam2" -c "ocaml-variants.$OPAM_VERSION" --disable-sandboxing
      if { ! $INTERACTIVE ; } && ! grep 'opam-init' "$EVEREST_ENV_DEST_FILE"  >/dev/null ; then
        # --auto-setup might not have worked, so manually do it here.
        # Do not expand variables in the textual output.
        echo '. "$HOME/.opam/opam-init/init.sh" > /dev/null 2>/dev/null' >> "$EVEREST_ENV_DEST_FILE"
      fi
      eval $(opam config env)
    else
      red "ERROR: no ocaml found in PATH"
      if is_osx; then
        echo "Hint: brew install ocaml opam"
      else
        echo "Please use your distribution's package management system to install ocaml and opam"
        echo "Note: on older Ubuntus, see https://launchpad.net/~avsm/+archive/ubuntu/ppa"
      fi
      exit 1
    fi

  else
    # OCaml; if this exits, set -e means this is a hard error
    ocaml -noinit -noprompt -stdin <<OCAML
      if Sys.ocaml_version < "$MINIMAL_OCAML_VERSION" then begin
        print_endline "ERROR: Everest needs OCaml >= $MINIMAL_OCAML_VERSION";
        print_endline ("You have OCaml " ^ Sys.ocaml_version);
        exit 1
      end
OCAML
    echo "... ocaml minimum version requirements met"
  fi

  # OCamlfind & extra packages. Required OPAM packages are stored in
  # [opam-packages], where each line is of the form:
  #   <ocamlfind-package-name> <SPACE> <opam-package-name>
  success_or "opam"
  if [ ! -d ~/.opam ]; then
    if is_windows; then
      echo "This is a Windows environment; not running opam init."
      echo "Please follow instructions for the installer you picked."
      echo "Hint: https://github.com/protz/ocaml-installer/wiki or https://fdopen.github.io/opam-repository-mingw/"
    else
      if_yes "opam init"
    fi
    eval $(opam config env)
  fi

  if ! command -v ocamlfind >/dev/null 2>&1; then
    magenta "ocamlfind not found!"
    if_yes "opam install ocamlfind"
  fi

  missing=false
  while read line; do
    ocamlfind_package=$(echo $line | cut -d " " -f 1)
    opam_package=$(echo $line | cut -d " " -f 2)
    if ! ocamlfind query $ocamlfind_package >/dev/null 2>&1; then
      red "ERROR: ocamlfind package $ocamlfind_package is not installed"
      missing=true
      break
    fi
  done < opam-packages
  if $missing; then
    if_yes "install_all_opam_packages"
  fi
  echo "... all $(cat opam-packages | wc -l) ocamlfind packages found"

  if is_windows && [ -d "/cygdrive/c/OCaml/lib/camlp4" ] && [[ $CAMLP4LIB == "" ]]; then
    red "Warning: seems like you're using the OCaml installer for windows"
    echo There is a bug in the installer -- please see \
      https://github.com/protz/ocaml-installer/wiki#configure-your-initial-opam-setup \
      and add \"export CAMLP4LIB=C:/OCaml/lib/camlp4\" in your "$EVEREST_ENV_DEST_FILE"
  fi

  if is_windows ; then
      # the latest ocaml-stdint segfaults on Windows with
      # 128-bit integers (confirmed on gcc-9 at least)
      # so we need to test whether it works, and if not,
      # then we pull a homemade patch that recompiles it with
      # C compiler optimizations disabled
      if ! [[ -d ocaml-stdint ]] ; then
          echo "... cloning tahina-pro/ocaml-stdint"
          try_git_clone "git@github.com:tahina-pro/ocaml-stdint.git" "https://github.com/tahina-pro/ocaml-stdint.git" ocaml-stdint
      fi
      echo "... building ocaml-stdint test"
      (cd ocaml-stdint && git clean -ffdx)
      ocamlfind ocamlopt -package str,qcheck,stdint ocaml-stdint/tests/stdint_test.ml -linkpkg -o ocaml-stdint/tests/stdint_test.exe
      echo "... running ocaml-stdint test"
      if
          { ocaml-stdint/tests/stdint_test.exe > /dev/null ; } ||
          [[ $? -le 1 ]] # tests fail, but should not segfault
      then
          echo "... ocaml-stdint works well"
      else
          magenta "ERROR: Your ocaml stdint package does not work with your C compiler."
          magenta "Do you want to have it recompiled with -O0 and reinstalled? [Yn]"
          prompt_yes true "exit 1"
          echo "... recompiling and reinstalling ocaml-stdint from tahina-pro/ocaml-stdint"
          (
              cd ocaml-stdint &&
              git clean -ffdx &&
              $MAKE &&
              $MAKE tests/stdint_test &&
              { { tests/stdint_test.exe > /dev/null ; } || [[ $? -le 1 ]] ; } &&
              dune install
          )
      fi
  fi

  do_update_z3

  check_no_slash () {
    for v; do
      if echo "${!v}" | grep -q '^/'; then
        red "You are on windows but your $v is a Cygwin-style path."
        red "Don't do that, follow the suggestion below."
        unset $v
      fi
    done
  }

  if is_windows; then
    check_no_slash FSTAR_EXE KRML_HOME EVERPARSE_HOME
  fi

  echo "Checking for gh (GitHub CLI)"
  if [[ -z "$everparse_do_release" ]] ; then
      echo "Check skipped, not releasing"
  elif command -v gh >/dev/null 2>&1 ; then
      echo "... gh found in PATH"
  else
      red "ERROR: gh (GitHub CLI) not found in PATH"
      if is_windows ; then
          gh_version=2.20.2
          magenta "Do you want to download gh $gh_version ?"
          prompt_yes true "exit 1"
          if ! [[ -d gh ]] ; then
              gh_zip=gh_${gh_version}_windows_amd64.zip
              wget "https://github.com/cli/cli/releases/download/v${gh_version}/${gh_zip}"
              unzip -d gh $gh_zip
          fi
          chmod +x gh/bin/gh.exe
          write_gh_env_dest_file
      else
          red "Please install it following https://github.com/cli/cli#installation"
          exit 1
      fi
  fi

  echo
  magenta "Remember to run source \"$EVEREST_ENV_DEST_FILE\" if it was modified!"
  local xpwd=""
  if is_windows; then
      xpwd="$(cygpath -m $(pwd))"
  else
      xpwd="$(pwd)"
  fi

  magenta "Note: you *may* want to add ${xpwd}/FStar/bin and ${xpwd}/karamel to your PATH"
  [ -n "${FSTAR_EXE}" ] || \
    magenta "Note: you *may* want to export FSTAR_EXE=${xpwd}/FStar/bin/fstar.exe"
  [ -n "${KRML_HOME}" ] || \
    magenta "Note: you *may* want to export KRML_HOME=${xpwd}/karamel"
}

symlink_clone_warned=false

check_subp_exists () {
  check_no_archive
  local r=$1
  if [ ! -d $r ]; then
    if [ -e $r ]; then
      red "$r exists but is not a directory, aborting"
      exit 1
    fi
    if ! $symlink_clone_warned; then
      echo Note: you\'re welcome to create symbolic links if you already have \
        cloned the repository elsewhere
      symlink_clone_warned=true
    fi
    try_git_clone ${repositories[$r]} ${https[$r]} $r
  fi
}

separator () {
  echo "================================================================================"
}

set_windows () {
  export EVEREST_WINDOWS=1
}

set_opt () {
  # Picked up by pretty much all the Makefiles
  export CFLAGS="-funroll-loops -fomit-frame-pointer -O3"
}

# ------------------------------------------------------------------------------
# Usage and parsing arguments
# ------------------------------------------------------------------------------

OPTIONS=j:k
LONGOPTS=yes,release,windows,openssl,opt,admit,no-vale-archive,no-z3

# Temporarily stores output to check for errors
# --alternative allows long options to start with a single '-'
! PARSED=$($GETOPT --alternative --options=$OPTIONS --longoptions=$LONGOPTS --name "$0" -- "$@")
if [[ ${PIPESTATUS[0]} -ne 0 ]]; then
    exit 2
fi

eval set -- "$PARSED"

# Read options until --
while true; do
    case "$1" in
        -j)
            parallel_opt="-j $2"
            set_make_opts
            shift 2
            ;;

        -k)
            keep_going_opt="-k"
            set_make_opts
            shift
            ;;

        -yes|--yes)
            make_non_interactive
            shift
            ;;

        (-release|--release)
            everparse_do_release=1
            shift
            ;;

        --no-z3)
            no_z3=true
            shift
            ;;

        --)
            shift
            break
            ;;
        *)
            echo "Unexpected error parsing options"
            exit 3
            ;;
    esac
done

# Handle commands
if [[ $# -eq 0 ]]; then
    exit 0
fi

while true; do
  if [[ $# -eq 0 ]]; then
    exit 0
  fi
  case "$1" in
    check)
      do_check
      ;;
    opam)
      install_all_opam_packages
      ;;

    z3)
      do_update_z3
      ;;

    *)
      print_usage
      exit 1
      ;;
  esac
  shift
done
