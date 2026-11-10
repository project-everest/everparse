#!/usr/bin/env python3
"""Deterministic DER mutations of the hand-written accept vectors.

Usage: mutate.py VECTOR_DIR OUT_JSON

Every mutation below breaks a DER rule whatever the type, so each mutated
vector is a `reject`, whatever the schema says:

  truncated            drop the last octet, so the outer length overruns the
                       input (X.690 8.1.1)
  length-nonminimal    outer length in a non-minimal long form (X.690 10.1)
  constructed-primitive
                       flip the primitive/constructed bit of the outer tag
                       (X.690 8.1.2.5; DER 10.2 for strings)
  tag-nonminimal       a low tag number (< 31) in the high-tag-number form
                       (X.690 8.1.2.2)
  length-indefinite    indefinite length on a constructed outer value
                       (X.690 10.1)
  inner-length-nonminimal
                       non-minimal long-form length on the first component
                       of a constructed value (X.690 10.1)
  trailing-data        two extra 00 octets at the end of a constructed
                       value. They form a TLV with tag [UNIVERSAL 0], which
                       X.690 8.1.2.2 Table 1 reserves for end-of-contents,
                       and X.680 25 and 27 forbid extra components without
                       an extension marker.
  inner-overrun        shorten a constructed value by one octet, so its
                       last component overruns it (X.690 8.1.1)

Values whose contents are opaque (ANY, EXTERNAL, EMBEDDED PDV, CHARACTER
STRING) are only mutated at the outer level. A top-level ANY is not mutated
at all, since any well-formed TLV is a valid ANY. A mutated encoding that
equals a hand-written vector of the same type is dropped.
"""

import glob
import json
import os
import sys

OPAQUE = {'ANY', 'ANY DEFINED BY', 'EXTERNAL', 'EMBEDDED PDV',
          'CHARACTER STRING'}
TOP_ANY = {'DiffAny.AnyT'}


def be(n):
    return n.to_bytes(max(1, (n.bit_length() + 7) // 8), 'big')


def enc_len(n):
    return bytes([n]) if n < 0x80 else bytes([0x80 | len(be(n))]) + be(n)


def nonminimal_len(n):
    """A long-form length one octet longer than the minimal encoding."""
    b = be(n) if n < 0x80 else b'\x00' + be(n)
    return bytes([0x80 | len(b)]) + b


def parse_tlv(data, off=0):
    """Return (tag_bytes, content_start, content_end) of the TLV at off."""
    start = off
    if data[off] & 0x1f == 0x1f:
        off += 1
        while data[off] & 0x80:
            off += 1
    off += 1
    tag = data[start:off]
    first = data[off]
    off += 1
    if first < 0x80:
        n = first
    else:
        k = first & 0x7f
        n = int.from_bytes(data[off:off + k], 'big')
        off += k
    return tag, off, off + n


def mutations(v):
    data = bytes.fromhex(v['hex'])
    tag, cs, ce = parse_tlv(data)
    if ce != len(data):
        return
    content = data[cs:ce]
    constructed = bool(tag[0] & 0x20)
    opaque = bool(OPAQUE & set(v['features']))

    def tlv(t, c):
        return t + enc_len(len(c)) + c

    yield 'truncated', data[:-1], [], 'X.690 8.1.1'
    yield ('length-nonminimal', tag + nonminimal_len(len(content)) + content,
           ['len.long'], 'X.690 10.1')
    yield ('constructed-primitive', tlv(bytes([tag[0] ^ 0x20]) + tag[1:], content),
           [], 'X.690 8.1.2.5, 10.2')
    if len(tag) == 1 and tag[0] & 0x1f < 31:
        yield ('tag-nonminimal', tlv(bytes([tag[0] | 0x1f, tag[0] & 0x1f]), content),
               ['id.high-tag'], 'X.690 8.1.2.2')
    if not constructed:
        return
    yield ('length-indefinite', tag + b'\x80' + content + b'\x00\x00', [],
           'X.690 10.1')
    if opaque or not content:
        return
    ctag, ccs, cce = parse_tlv(content)
    first = ctag + nonminimal_len(cce - ccs) + content[ccs:cce]
    yield ('inner-length-nonminimal', tlv(tag, first + content[cce:]),
           ['len.long'], 'X.690 10.1')
    yield ('trailing-data', tlv(tag, content + b'\x00\x00'), [],
           'X.690 8.1.2.2, X.680 25, 27')
    yield 'inner-overrun', tlv(tag, content[:-1]), [], 'X.690 8.1.1'


def main():
    vector_dir, out = sys.argv[1:3]
    base = []
    for path in sorted(glob.glob(os.path.join(vector_dir, '*.json'))):
        with open(path) as f:
            base += json.load(f)['vectors']
    known = {(v['type'], v['hex'].lower()) for v in base}
    vectors = []
    for v in base:
        if v['expect'] != 'accept' or v['type'] in TOP_ANY:
            continue
        for name, data, extra, clause in mutations(v):
            h = data.hex()
            if (v['type'], h) in known:
                continue
            known.add((v['type'], h))
            vectors.append({
                'id': f'mut/{name}/{v["id"]}',
                'type': v['type'],
                'hex': h,
                'expect': 'reject',
                'clause': clause,
                'features': v['features'] + [f for f in extra if f not in v['features']],
                'mutation': name,
                'notes': f'generated by gen/mutate.py from {v["id"]}',
            })
    os.makedirs(os.path.dirname(out) or '.', exist_ok=True)
    with open(out, 'w') as f:
        json.dump({'vectors': vectors}, f, indent=1)
    print(f'mutate.py: {len(vectors)} vectors -> {out}')


if __name__ == '__main__':
    main()
