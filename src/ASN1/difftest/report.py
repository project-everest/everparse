#!/usr/bin/env python3
"""ASN.1 DER differential tests: manifest assembly, reporting and gating.

  report.py manifest VECTOR_DIR FEATURES OUT_MANIFEST [--gen DIR]...
      Merge and validate VECTOR_DIR/*.json (and DIR/*.json for each
      generated-vector directory DIR) into a single manifest.
  report.py filter --manifest M --known FILE --impl IMPL OUT_MANIFEST
      Write the vectors of M that are not in the baseline for IMPL.
  report.py check   [common options] [--new-only] [--ours-results DIR]
      Compare all results with the expected verdicts and with the triaged
      baseline; write a markdown report; exit 1 on any regression.
      With --new-only, the other implementations were run on `filter`ed
      manifests: their baseline vectors are skipped, and rule (c) is not
      checked. Our results are read from --ours-results (default
      --results), and must cover every vector.
  report.py rebaseline [common options]
      Rewrite the baseline: drop stale entries, add new discrepancies as
      "untriaged" (which `check` rejects until they are classified).

Common options: --manifest M --capabilities DIR --known FILE --results DIR
                [--report FILE]

Gating rules of `check`:
  (a) our verdict must equal the expected (X.690) verdict on every vector;
  (b) every discrepancy of another implementation must be in the baseline,
      with a class other than "untriaged";
  (c) every baseline entry of an implementation that ran must still occur
      (not checked with --new-only).
Implementations whose results file is absent (runner skipped) are ignored.
"""

import argparse
import glob
import json
import os
import re
import sys
from collections import defaultdict

IMPLS = ['ours', 'asn1tools', 'rasn', 'asn1-rs']
CLASSES = {
    'harness': 'runner or schema-translation bug (to fix)',
    'manifest': 'expected verdict wrong (to fix)',
    'policy': 'ours stricter than X.690 by design',
    'ambiguity': 'X.690 unclear',
    'documented-leniency': 'leniency documented by the implementation',
    'bug-asn1tools': 'asn1tools bug',
    'bug-rasn': 'rasn bug',
    'bug-asn1-rs': 'asn1-rs bug',
    'untriaged': 'not yet triaged (check fails)',
}
VECTOR_FIELDS = {'id', 'type', 'hex', 'expect', 'clause', 'features',
                 'mutation', 'notes', 'value'}


def fail(msg):
    print(f'report.py: {msg}', file=sys.stderr)
    sys.exit(2)


def load_json(path):
    with open(path) as f:
        return json.load(f)


def cmd_manifest(args):
    features = set(load_json(args.features)['features'])
    vectors, ids = [], set()
    paths = [path for d in [args.vector_dir] + args.gen
             for path in sorted(glob.glob(os.path.join(d, '*.json')))]
    for path in paths:
        for v in load_json(path)['vectors']:
            where = f'{path}: {v.get("id")}'
            for k in ('id', 'type', 'hex', 'expect', 'clause', 'features'):
                if k not in v:
                    fail(f'{where}: missing field {k}')
            if set(v) - VECTOR_FIELDS:
                fail(f'{where}: unknown fields {set(v) - VECTOR_FIELDS}')
            if v['id'] in ids:
                fail(f'{where}: duplicate id')
            ids.add(v['id'])
            if v['expect'] not in ('accept', 'reject'):
                fail(f'{where}: bad expect')
            if not re.fullmatch(r'[A-Za-z][\w-]*\.[A-Za-z][\w-]*', v['type']):
                fail(f'{where}: type must be Module.Type')
            h = re.sub(r'\s', '', v['hex'])
            if not re.fullmatch(r'([0-9a-fA-F]{2})*', h):
                fail(f'{where}: bad hex')
            v['hex'] = h.lower()
            unknown = set(v['features']) - features
            if unknown or not v['features']:
                fail(f'{where}: unknown or no features {unknown}')
            vectors.append(v)
    with open(args.out, 'w') as f:
        json.dump({'vectors': vectors}, f, indent=1)
    print(f'manifest: {len(vectors)} vectors -> {args.out}')


def load_results(results_dir, ours_dir=None):
    results = {}
    for impl in IMPLS:
        d = ours_dir if impl == 'ours' and ours_dir else results_dir
        path = os.path.join(d, f'{impl}.jsonl')
        if os.path.exists(path):
            with open(path) as f:
                results[impl] = {r['id']: r for r in map(json.loads, f)}
    return results


def load_capabilities(cap_dir, impl):
    path = os.path.join(cap_dir, f'{impl}.json')
    caps = load_json(path)['features'] if os.path.exists(path) else {}
    return {f for f, c in caps.items() if c['status'] in ('supported', 'partial')}


def collect(args, skip=frozenset()):
    """Return (ours_failures, discrepancies, stats, ran).
    Pairs (impl, id) in `skip` are not checked (see --new-only)."""
    vectors = load_json(args.manifest)['vectors']
    results = load_results(args.results, getattr(args, 'ours_results', None))
    if 'ours' not in results:
        fail(f'no results for ours in {args.results}')
    ours_failures, discrepancies = [], {}
    stats = {}
    for impl, res in results.items():
        caps = None if impl == 'ours' else load_capabilities(args.capabilities, impl)
        st = stats[impl] = defaultdict(int)
        for v in vectors:
            if caps is not None and not set(v['features']) <= caps:
                st['skipped (capabilities)'] += 1
                continue
            if (impl, v['id']) in skip:
                st['skipped (known)'] += 1
                continue
            r = res.get(v['id'])
            got = r['verdict'] if r else 'missing'
            st['run'] += 1
            if got == v['expect']:
                st['agree'] += 1
                continue
            if impl == 'ours':
                ours_failures.append((v, r))
            else:
                discrepancies[(impl, v['id'])] = (v, got, r)
    return ours_failures, discrepancies, stats, set(results)


def load_known(path):
    if not os.path.exists(path):
        return {}
    known = {}
    for e in load_json(path)['discrepancies']:
        if e['class'] not in CLASSES:
            fail(f'{path}: {e["impl"]} {e["id"]}: unknown class {e["class"]}')
        known[(e['impl'], e['id'])] = e
    return known


def write_report(path, vectors_by_id, ours_failures, discrepancies, known, stats, problems):
    lines = ['# ASN.1 DER differential test report', '',
             '| implementation | run | agree with X.690 | known discrepancies | new | skipped (capabilities) | skipped (known) |',
             '|---|---|---|---|---|---|---|']
    for impl in IMPLS:
        if impl not in stats:
            lines.append(f'| {impl} | not run | | | | | |')
            continue
        st = stats[impl]
        nk = sum(1 for (i, vid) in discrepancies if i == impl and (i, vid) in known)
        nn = (len(ours_failures) if impl == 'ours' else
              sum(1 for (i, vid) in discrepancies if i == impl and (i, vid) not in known))
        lines.append(f'| {impl} | {st["run"]} | {st["agree"]} | {nk} | {nn} | {st["skipped (capabilities)"]} | {st["skipped (known)"]} |')
    lines += ['', '## Problems (check fails)', '']
    lines += [f'- {p}' for p in problems] or ['None.']
    clusters = defaultdict(list)
    for (impl, vid), (v, got, _) in sorted(discrepancies.items()):
        cls = known.get((impl, vid), {}).get('class', 'NEW')
        clusters[(impl, cls, v.get('mutation') or 'positive', got)].append(vid)
    lines += ['', '## Discrepancies by cluster', '',
              '| implementation | class | mutation | got | vectors |', '|---|---|---|---|---|']
    for (impl, cls, mut, got), ids in sorted(clusters.items()):
        lines.append(f'| {impl} | {cls} | {mut} | {got} | {len(ids)}: {", ".join(ids[:5])}{" ..." if len(ids) > 5 else ""} |')
    lines += ['', '## Discrepancy details', '']
    for (impl, vid), (v, got, r) in sorted(discrepancies.items()):
        k = known.get((impl, vid))
        lines.append(f'- `{vid}` {impl}: expected {v["expect"]} ({v["clause"]}), got {got}'
                     + (f' [{k["class"]}]' if k else ' [NEW]')
                     + (f': {r["error"]}' if r and r.get('error') else ''))
    with open(path, 'w') as f:
        f.write('\n'.join(lines) + '\n')


def cmd_check(args):
    vectors = load_json(args.manifest)['vectors']
    vectors_by_id = {v['id']: v for v in vectors}
    known = load_known(args.known)
    skip = frozenset(known) if args.new_only else frozenset()
    ours_failures, discrepancies, stats, ran = collect(args, skip)
    problems = []
    for v, r in ours_failures:
        problems.append(f'ours: `{v["id"]}` expected {v["expect"]} ({v["clause"]}), '
                        f'got {r["verdict"] if r else "missing"}')
    for key, (v, got, _) in sorted(discrepancies.items()):
        e = known.get(key)
        if e is None:
            problems.append(f'{key[0]}: `{key[1]}` new discrepancy: expected {v["expect"]}, got {got}')
        elif e['got'] != got:
            problems.append(f'{key[0]}: `{key[1]}` baseline says {e["got"]}, got {got}')
        elif e['class'] == 'untriaged':
            problems.append(f'{key[0]}: `{key[1]}` untriaged discrepancy')
    for key, e in sorted(known.items()):
        if args.new_only:
            if key[0] in ran and e['class'] == 'untriaged':
                problems.append(f'{key[0]}: `{key[1]}` untriaged discrepancy')
        elif key[0] in ran and key not in discrepancies:
            problems.append(f'{key[0]}: `{key[1]}` stale baseline entry (no longer a discrepancy, '
                            f'or vector removed); run `make rebaseline`')
    if args.report:
        write_report(args.report, vectors_by_id, ours_failures, discrepancies, known, stats, problems)
    for impl in IMPLS:
        if impl in stats:
            st = stats[impl]
            print(f'{impl:10} run {st["run"]:4}  agree {st["agree"]:4}  '
                  f'skipped {st["skipped (capabilities)"]:4}'
                  + (f'  known (not run) {st["skipped (known)"]:4}' if args.new_only else ''))
        else:
            print(f'{impl:10} not run')
    for p in problems:
        print(f'FAIL {p}')
    if problems:
        print(f'difftest: {len(problems)} problem(s)' + (f', see {args.report}' if args.report else ''))
        sys.exit(1)
    print('difftest: OK' + (f', report in {args.report}' if args.report else ''))


def cmd_filter(args):
    known = {vid for (impl, vid) in load_known(args.known) if impl == args.impl}
    vectors = [v for v in load_json(args.manifest)['vectors'] if v['id'] not in known]
    with open(args.out, 'w') as f:
        json.dump({'vectors': vectors}, f, indent=1)
    print(f'filter: {len(vectors)} vectors not in the {args.impl} baseline -> {args.out}')


def cmd_rebaseline(args):
    if args.new_only:
        fail('rebaseline needs the results of every vector (no --new-only)')
    ours_failures, discrepancies, _, ran = collect(args)
    if ours_failures:
        fail('refusing to rebaseline while ours disagrees with the manifest')
    known = load_known(args.known)
    entries = []
    for key, e in known.items():
        if key[0] not in ran:
            entries.append(e)  # runner not run: keep as is
    for (impl, vid), (v, got, r) in discrepancies.items():
        e = known.get((impl, vid))
        if e is None or e['got'] != got:
            e = {'impl': impl, 'id': vid, 'got': got, 'class': 'untriaged',
                 'rationale': (r or {}).get('error', '')}
        entries.append(e)
    entries.sort(key=lambda e: (e['impl'], e['id']))
    with open(args.known, 'w') as f:
        json.dump({'discrepancies': entries}, f, indent=1)
        f.write('\n')
    print(f'rebaseline: {len(entries)} entries -> {args.known}')


def main():
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest='cmd', required=True)
    m = sub.add_parser('manifest')
    m.add_argument('vector_dir')
    m.add_argument('features')
    m.add_argument('out')
    m.add_argument('--gen', action='append', default=[])
    fl = sub.add_parser('filter')
    fl.add_argument('--manifest', required=True)
    fl.add_argument('--known', required=True)
    fl.add_argument('--impl', required=True, choices=IMPLS[1:])
    fl.add_argument('out')
    for name in ('check', 'rebaseline'):
        c = sub.add_parser(name)
        c.add_argument('--manifest', required=True)
        c.add_argument('--capabilities', required=True)
        c.add_argument('--known', required=True)
        c.add_argument('--results', required=True)
        c.add_argument('--report')
        c.add_argument('--ours-results')
        c.add_argument('--new-only', action='store_true')
    args = p.parse_args()
    {'manifest': cmd_manifest, 'filter': cmd_filter, 'check': cmd_check,
     'rebaseline': cmd_rebaseline}[args.cmd](args)


if __name__ == '__main__':
    main()
