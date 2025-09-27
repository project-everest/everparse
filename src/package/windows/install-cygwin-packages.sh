#!/usr/bin/env bash
set -e
set -x

unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"

cygwin_has () {
  (( $(cygcheck -c -d $1 | wc -l) > 2 ))
}

cygsetup="setup-x86_64.exe"
cygsetup_args="--no-desktop --no-shortcuts --no-startmenu --wait --quiet-mode"

# Find Cygwin's setup utility, or download it from the internet.
# Success: writes the path to Cygwin's setup in $cygsetup
# Failure: aborts.
found=false
if cygsetup="$(which $cygsetup)" ; then
    found=true
fi

if ! $found ; then
    for s in "$USERPROFILE/Desktop/setup-x86_64.exe" "$USERPROFILE/Downloads/setup-x86_64.exe" "./setup-x86_64.exe" "c:/cygwin64/setup-x86_64.exe" "c:/cygwin/setup-x86_64.exe" "$USERPROFILE/Desktop/cygwinsetup.exe" "$USERPROFILE/Downloads/cygwinsetup.exe" "./cygwinsetup.exe" "c:/cygwin64/cygwinsetup.exe" "c:/cygwin/cygwinsetup.exe"; do
	if [ -x "$s" ]; then
	    echo "Found $cygsetup"
	    found=true
	    cygsetup="$s"
	fi
    done
fi

if ! $found; then
    echo "Cygwin setup not found, downloading it"
    if ! command -v wget >/dev/null 2>&1; then
	echo "ERROR: please either place cygwin's setup-x86_64.exe in your Downloads or Desktop folder, or install wget via cygwin's setup"
    fi
    cygsetup=./setup-x86_64.exe
    curl --output $cygsetup "https://cygwin.com/setup-x86_64.exe"
fi

chmod a+x "$cygsetup"
exec "$cygsetup" $cygsetup_args --packages=$(cat cygwin-packages | tr '\n' ,)
