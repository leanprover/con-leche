#!/usr/bin/env python3
"""Build the task #480 fixtures: the verdict of a stream whose failure is a
job of the check phase, against a failure elsewhere in the fold.

  mk_defer_order.py tests/e2e

writes, into that directory:

* defer_value_reject_then_axiom.ndjson: a definition whose value has the
  wrong type (reject), then a non-standard axiom (decline);
* defer_axiom_then_value_reject.ndjson: the same two records swapped;
* natop_perturbed_used_later.ndjson: `nat_land_perturbed` (the pinned
  `Nat.land` with a type-correct but different body) followed by the
  `nat_land_ok` theorem `Nat.land 12 10 = 8` by `Eq.refl`, which may fire
  the operation's literal fast path before the operation's job has run;
* natop_perturbed_later_reject.ndjson: the same, the theorem stating
  `Nat.land 12 10 = 9`, wrong whatever the operation does.
"""
import gzip
import json
import os
import sys

META = ('{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},'
        '"format":{"version":"3.1.0"},"lean":{"githash":'
        '"f72c35b3f637c8c6571d353742168ab66cc22c00","version":"4.29.1"}}}')


def write(path, lines):
    with open(path, 'w') as f:
        f.write('\n'.join(lines) + '\n')


def small(out, value_first):
    """A stream of two faulty records, in either order."""
    head = [
        META,
        '{"in":1,"str":{"pre":0,"str":"customAx"}}',
        '{"in":2,"str":{"pre":0,"str":"bad"}}',
        '{"ie":0,"sort":0}',
    ]
    axiom = '{"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":0}}'
    # `def bad : Prop := Prop`: the value is a `Type`, not a proposition
    bad = ('{"def":{"all":[2],"hints":"abbrev","levelParams":[],"name":2,'
           '"safety":"safe","type":0,"value":0}}')
    write(out, head + ([bad, axiom] if value_first else [axiom, bad]))


def ids_at_least(line, n, shift):
    """Shift every expression id >= n in a record by `shift`."""
    r = json.loads(line)

    def s(x):
        return x + shift if x >= n else x

    if 'ie' in r:
        r['ie'] = s(r['ie'])
        if 'app' in r:
            r['app']['fn'] = s(r['app']['fn'])
            r['app']['arg'] = s(r['app']['arg'])
    if 'thm' in r:
        r['thm']['type'] = s(r['thm']['type'])
        r['thm']['value'] = s(r['thm']['value'])
    return json.dumps(r, separators=(',', ':'))


def read_gz(path):
    with gzip.open(path, 'rt') as f:
        return f.read().splitlines()


def natop(d):
    ok = read_gz(os.path.join(d, 'nat_land_ok.ndjson.gz'))
    pert = read_gz(os.path.join(d, 'nat_land_perturbed.ndjson.gz'))
    # the theorem's records: everything after the operation's own record
    i = next(k for k, l in enumerate(ok) if '"def"' in l and '"name":4197' in l)
    tail = ok[i + 1:]
    base = json.loads(ok[i + 1])['ie']
    top = max(json.loads(l)['ie'] for l in pert if '"ie"' in l)
    tail = [ids_at_least(l, base, top + 1 - base) for l in tail]
    write(os.path.join(d, 'natop_perturbed_used_later.ndjson'), pert + tail)
    # the theorem's type at another literal: the last `natVal` the statement
    # reads is `8`, the proof's `Eq.refl` keeps it
    lit = top + len(tail) + 1
    eight = next(json.loads(l)['ie'] for l in tail if '"natVal":"8"' in l)
    wrong = []
    for l in tail:
        r = json.loads(l)
        if 'app' in r and r['app']['arg'] == eight and 'thm' not in r:
            # the statement's `Eq Nat (land 12 10) 8`: its right-hand side is
            # the first application of the literal `8`, the proof's the second
            if not wrong or not any('"natVal":"9"' in w for w in wrong):
                wrong.append(json.dumps({'ie': lit, 'natVal': '9'}, separators=(',', ':')))
                r['app']['arg'] = lit
                wrong.append(json.dumps(r, separators=(',', ':')))
                continue
        wrong.append(l)
    write(os.path.join(d, 'natop_perturbed_later_reject.ndjson'), pert + wrong)


def main():
    d = sys.argv[1]
    small(os.path.join(d, 'defer_value_reject_then_axiom.ndjson'), True)
    small(os.path.join(d, 'defer_axiom_then_value_reject.ndjson'), False)
    natop(d)


main()
