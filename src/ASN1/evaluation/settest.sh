#!/usr/bin/env bash
# Tests for SET { ... } (ASN1.SetTest):
#   SetTest ::= SET {
#     a [0] IMPLICIT INTEGER,
#     b [1] IMPLICIT INTEGER OPTIONAL,
#     c CHOICE { c2 [2] IMPLICIT BOOLEAN, c5 [5] IMPLICIT NULL },
#     d [3] IMPLICIT BOOLEAN DEFAULT TRUE,
#     e OCTET STRING OPTIONAL }
set -u
cd "$(dirname "$0")"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
failed=0

check () {
  local expected=$1 name=$2 hex=$3
  local f="$tmp/$name.der"
  # Decode hex in pure bash (xxd is not available everywhere, e.g. in CI)
  hex=${hex// /}
  local esc="" i
  for (( i = 0; i < ${#hex}; i += 2 )); do esc+="\\x${hex:i:2}"; done
  printf "$esc" > "$f"
  if ./ASN1_Parser.exe SETTEST "$f" > /dev/null ; then actual=accept ; else actual=reject ; fi
  if [ "$actual" = "$expected" ] ; then
    echo "OK   $expected $name"
  else
    echo "FAIL $name: expected $expected, got $actual"
    failed=1
  fi
}

# Components are sorted by tag: UNIVERSAL e (04) first, then [0] [1] [2] [3] [5]
check accept minimal          "3106800105 8201ff"
check accept all              "3110 0402abcd 800105 810107 8201ff 830100"
check accept choice_after_d   "3108 800105 830100 8500"
check accept choice_c5        "3105 800105 8500"
check reject out_of_order     "3106 8201ff 800105"
check reject duplicate        "3109 800105 800106 8201ff"
check reject choice_twice     "3108 800105 8201ff 8500"
check reject missing_a        "3103 8201ff"
check reject missing_c        "3103 800105"
check reject default_encoded  "3109 800105 8201ff 8301ff"
check reject unknown_tag      "3109 800105 8201ff 840100"
check reject universal_last   "3108 800105 8201ff 0400"
check reject sequence_tag     "3006 800105 8201ff"

exit $failed
