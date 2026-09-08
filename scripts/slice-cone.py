#!/usr/bin/env python3
"""Cut the dependency CONE of one or more declarations out of a
lean4export NDJSON stream (task #224).

    scripts/slice-cone.py STREAM.ndjson TARGET[,TARGET…] OUT.ndjson

THE COMPANION TOOL is `scripts/resume_slice.py`, which cuts a stream's
*suffix* (everything from a cut point on, plus what that suffix still
needs).  This one cuts a *prefix*: everything the named declarations
need, and nothing else.  (Task #224 note: `resume_slice.py` still reads
the PREPROCESSED record layout described below and dies with `unknown
record kind 'forallE'` on a raw stream; that repair is a separate item.)

THE CONE.  The output is the shortest valid prefix-slice of the stream
that ends with the last named target's own record:

* a declaration record is kept iff a target reaches it through the
  constants named in kept declarations' types, values and recursor
  rules — plus, for an inductive block, its type formers, constructors
  and recursors, all of which travel as ONE record and are therefore
  kept together;
* an expression (`ie`) record is kept iff a kept declaration reaches it;
  ids are never renumbered, so the unkept ones simply vanish and the
  survivors still refer to each other correctly;
* every name (`in`), level (`il`) and `meta` record is kept verbatim.
  They are a few percent of the stream, so no name or level closure is
  worth computing;
* nothing after the last target's record is kept.

There is NO `_model` companion rule.  Until task #219 a `X._model`
record had to be dragged in with `X` because the install dispatch read
it; models are generated in-process now and a stream `_model` record,
if a stream still has one, is an ordinary declaration.

THE FORMAT.  lean4export 3.x NDJSON, one JSON object per line, as
`_tmp/mathlib-scoping/mathlib-full.ndjson`, `_tmp/init-exports/*.ndjson`
and the fixtures under `tests/` have it.  The reader is INDEPENDENT OF
KEY ORDER, which is the bug this file was written to end.

RAW `lean4export` writes every object's keys ALPHABETICALLY, so an
expression record's `"ie"` tag comes first only when the node kind sorts
after it (`{"ie":57,"proj":{…}}`) and LAST when it sorts before
(`{"app":{"arg":3,"fn":7},"ie":8}` — and `app` is four records in five).
The now-retired `con-leche-preprocess` re-serialised every record with
the tag FIRST (`{"ie":5,"app":{"arg":1,"fn":4}}`), and the three `_tmp/`
generations of this script were written against those PREPROCESSED
streams: they tested `line.startswith(b'{"ie":')`, so on a raw stream
every `app`/`bvar`/`const`/`forallE`/`lam` record fell through to the
declaration path and the run died with `TypeError: 'int' object is not
subscriptable` at `r[k]["name"]` on the first `{"bvar":0,"ie":3}`.  The
preprocessor went at task #207 and every stream is raw now, so nothing
in `_tmp/` still ran.  `meta` is no help in telling the two apart — the
preprocessor copied it verbatim (both say lean4export 3.1.0).

A record is therefore classified here by which tag it CONTAINS, not by
which comes first, and both layouts read.

THE METHOD (why "fast").  Two forward passes over the file and no
seeking: pass 1 builds a compact array form of the expression DAG
(`array('i')` child-list + per-node constant reference) and an index of
the declaration records; pass 2 marks the cone in memory; pass 3
re-reads the file and emits.  Only the PREFIX up to the last target is
ever indexed — the reader stops there — so the cost tracks the target's
depth in the stream, not the file's size: a 713 k-line prefix (670 k
expression nodes, 5 k declarations) of `slice-small.ndjson` slices in
2.1 s at 74 MB peak RSS.  A target deep in full Mathlib is a different
matter; give it room.
"""
import argparse
import json
import re
import sys
from array import array

IE_RE = re.compile(rb'"ie":(\d+)[,}]')
KIDS_RE = re.compile(rb'"(?:fn|arg|body|type|value|struct)":(\d+)')
CONST_RE = re.compile(rb'"const":\{"name":(\d+)[,}]')
PROJ_RE = re.compile(rb'"typeName":(\d+)')
DECLK_RE = re.compile(rb'"(?:type|value|rhs)":(\d+)')


def is_name(line):        # {"in":N,"str":{…}} / {"in":N,"num":{…}}
    return line.startswith(b'{"in":')


def is_level(line):       # {"il":N,"succ":…} etc.
    return line.startswith(b'{"il":')


def is_meta(line):
    return line.startswith(b'{"meta":')


def is_expr(line):
    # Key order is alphabetical, so `"ie":` may sit anywhere; but a name
    # or level record always leads with its own tag (`in`/`il` sort
    # before every sibling key), which is what keeps a name whose string
    # happens to spell `"ie":` out of this test.
    return b'"ie":' in line


def main(argv=None):
    ap = argparse.ArgumentParser(
        prog='slice-cone.py',
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('stream', metavar='STREAM.ndjson',
                    help='a lean4export 3.x NDJSON stream (key order '
                         'does not matter)')
    ap.add_argument('targets', metavar='TARGET[,TARGET...]',
                    help='comma-separated declaration names; the slice '
                         'ends at the last one to appear')
    ap.add_argument('out', metavar='OUT.ndjson',
                    help='where to write the slice')
    ap.add_argument('-q', '--quiet', action='store_true',
                    help='do not print the per-pass counts on stderr')
    a = ap.parse_args(argv)

    def log(msg):
        if not a.quiet:
            print(msg, file=sys.stderr)

    targets = set(a.targets.split(','))
    found = set()

    # ---- names, resolved lazily up the `pre` chain
    names = ['']
    npre = array('i', [0])
    resolved = {0: ''}

    def nm(i):
        r = resolved.get(i)
        if r is not None:
            return r
        chain = []
        j = i
        while j not in resolved:
            chain.append(j)
            j = npre[j]
        s = resolved[j]
        for k in reversed(chain):
            s = (s + '.' if s else '') + names[k]
            resolved[k] = s
        return s

    # ---- the expression DAG, flattened: kid_flat[kid_off[i]:kid_off[i+1]]
    # are node i's child expr ids, cref[i] is the name id it references
    # (a `const` name or a `proj` type name), -1 if none.
    kid_flat = array('i')
    kid_off = array('l', [0])
    cref = array('i')

    decl_line = {}        # line index -> the parsed record
    decl_names = {}       # line index -> the names it declares
    decl_of_name = {}
    target_line = None

    # ------------------------------------------------- PASS 1: index
    with open(a.stream, 'rb') as f:
        for li, line in enumerate(f):
            if is_name(line):
                r = json.loads(line)
                i = r['in']
                while len(names) <= i:
                    names.append('')
                    npre.append(0)
                if 'str' in r:
                    npre[i] = r['str']['pre']
                    names[i] = r['str']['str']
                else:
                    npre[i] = r['num']['pre']
                    names[i] = str(r['num']['i'])
                continue
            if is_level(line) or is_meta(line):
                continue
            if is_expr(line):
                eid = int(IE_RE.search(line).group(1))
                while len(kid_off) <= eid:      # ids are dense, but be safe
                    kid_off.append(len(kid_flat))
                    cref.append(-1)
                assert len(kid_off) == eid + 1, (eid, len(kid_off))
                c = -1
                if b'"strVal":' not in line:
                    # A `strVal` node carries arbitrary text, which could
                    # spell any of the keys below; it has no children and
                    # no constant reference, so skip it wholesale.
                    for cs in KIDS_RE.findall(line):
                        kid_flat.append(int(cs))
                    cm = CONST_RE.search(line)
                    if cm:
                        c = int(cm.group(1))
                    else:
                        pm = PROJ_RE.search(line)
                        if pm:
                            c = int(pm.group(1))
                kid_off.append(len(kid_flat))
                cref.append(c)
                continue
            # ---- a declaration record
            r = json.loads(line)
            k = next(iter(r))
            if k == 'inductive':
                b = r['inductive']
                new = ([nm(t['name']) for t in b['types']] +
                       [nm(c['name']) for c in b['ctors']] +
                       [nm(x['name']) for x in b.get('recs', [])])
            elif isinstance(r[k], dict) and 'name' in r[k]:
                new = [nm(r[k]['name'])]
            else:
                sys.exit(f'{a.stream}:{li + 1}: unrecognised record `{k}` '
                         f'-- has the export format changed again?')
            decl_line[li] = r
            decl_names[li] = new
            for n in new:
                decl_of_name.setdefault(n, li)
                if n in targets:
                    found.add(n)
                    target_line = li
            if found == targets:
                break
    if found != targets:
        sys.exit(f'targets not found: {sorted(targets - found)}')
    log(f'pass 1: {len(names)} names, {len(decl_line)} decls, '
        f'{len(kid_off) - 1} expr nodes, last target at line '
        f'{target_line + 1}')

    # ------------------------------------------------- PASS 2: mark
    nexpr = len(kid_off) - 1
    seen = bytearray(nexpr)
    kept_e = set()
    kept_decl = set()
    want = list(targets)

    def walk_expr(root):
        st = [root]
        while st:
            e = st.pop()
            if e >= nexpr or seen[e]:
                continue
            seen[e] = 1
            kept_e.add(e)
            c = cref[e]
            if c >= 0:
                want.append(nm(c))
            for j in range(kid_off[e], kid_off[e + 1]):
                st.append(kid_flat[j])

    def keep_decl(li):
        if li in kept_decl:
            return
        kept_decl.add(li)
        r = decl_line[li]
        for cs in DECLK_RE.findall(
                json.dumps(r, separators=(',', ':')).encode()):
            walk_expr(int(cs))
        k = next(iter(r))
        if k == 'inductive':
            b = r['inductive']
            for t in b['types']:
                for x in t['all']:
                    want.append(nm(x))
                for c in t['ctors']:
                    want.append(nm(c))
            for c in b['ctors']:
                want.append(nm(c['induct']))
            for x in b.get('recs', []):
                for y in x['all']:
                    want.append(nm(y))
                for ru in x['rules']:
                    want.append(nm(ru['ctor']))

    while want:
        n = want.pop()
        li = decl_of_name.get(n)
        if li is not None and li not in kept_decl:
            keep_decl(li)
    log(f'pass 2: {len(kept_decl)} decls, {len(kept_e)} expr nodes marked')

    # ------------------------------------------------- PASS 3: emit
    out_records = 0
    with open(a.stream, 'rb') as f, open(a.out, 'wb') as fo:
        for li, line in enumerate(f):
            if is_name(line) or is_level(line) or is_meta(line):
                fo.write(line)
                out_records += 1
            elif is_expr(line):
                if int(IE_RE.search(line).group(1)) in kept_e:
                    fo.write(line)
                    out_records += 1
            elif li in kept_decl:
                fo.write(line)
                out_records += 1
            if li == target_line:
                break
    log(f'pass 3: {out_records} records written to {a.out} '
        f'({len(kept_decl)} declaration records)')


if __name__ == '__main__':
    main()
