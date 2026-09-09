#!/usr/bin/env python3
"""Differential harness for the byte recogniser (task #264).

Two builds of the checker read the same mutated stream and must agree
on the exit code and on the whole of stdout+stderr — which, for a
syntactic failure, carries the line number, the error tag and the BYTE
OFFSET, so a classifier that mis-lengths a key by one byte is caught
even where the verdict happens to agree.  That is what makes this a
usable acceptance gate for a change inside `ConLeche/Frontend/Scan`
that is meant to be observationally identical.

    scripts/scan-differential.py harvest DIR
    scripts/scan-differential.py keysweep OLD NEW DIR
    scripts/scan-differential.py fuzz     OLD NEW N DIR
    scripts/scan-differential.py stream   OLD NEW N FIXTURE...

`harvest` writes `DIR/header.txt` and `DIR/corpus.txt`: one shortest
representative record per key-shape, taken from `tests/e2e`,
`tests/arena` and `_tmp/arena-tests/good`, which between them use
every key of the dialect.  A case is then the header plus ONE mutated
record, so the mutation is always reached — `stream` instead mutates
one line of a whole fixture, which reaches the deeper slot loops.

`keysweep` is exhaustive where it matters: every one of the 66 key
spellings substituted into every key span of every record, and for
every third record each spelling also truncated at either end,
extended at either end, and each of its positions replaced by one of
four letters.  That walks the classifier's whole (first byte, length)
table together with its near misses.  `fuzz` is random: a byte
substituted, inserted or deleted, half the time inside a key, plus
whole-key replacement by another dialect key, a dialect key with one
letter changed, or a random letter run.

The OLD binary is built from the revision under comparison, e.g.
`git archive <sha> | tar -x -C … && lake build`, or simply copied out
of the main checkout's `.lake/build/bin` before the lane's own build.
"""

import glob, os, random, re, subprocess, sys, tempfile

KEYS = ("all app arg axiom binderInfo body bvar cidx const ctor ctors def fn "
        "forallE hints i idx ie il imax in induct inductive isRec isReflexive "
        "isUnsafe k kind lam letE levelParams max meta name natVal nfields "
        "nondep num numFields numIndices numMinors numMotives numNested "
        "numParams opaque param pre proj pw quot recs regular rhs rules "
        "safety sort str strVal struct succ thm type typeName types us value"
        ).split()
LET = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'
ALPH = bytes(b'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789'
             b'"{}[],:\\ \t')


def key_spans(line):
    """(open-quote, close-quote) of every quoted span followed by `:`."""
    out, i = [], 0
    while True:
        s = line.find(b'"', i)
        if s < 0:
            break
        e = line.find(b'"', s + 1)
        if e < 0:
            break
        j = e + 1
        while j < len(line) and line[j] in b' \t':
            j += 1
        if j < len(line) and line[j:j+1] == b':':
            out.append((s, e))
        i = e + 1
    return out


def harvest(outdir):
    seen, hdr = {}, None
    pats = ('tests/e2e/*.ndjson', 'tests/arena/*.ndjson',
            '_tmp/arena-tests/good/*.ndjson')
    for f in sorted(sum((glob.glob(p) for p in pats), [])):
        for l in open(f, 'rb').read().split(b'\n'):
            if not l.strip():
                continue
            if hdr is None and l.startswith(b'{"meta"'):
                hdr = l
            ks = tuple(sorted(set(re.findall(rb'"([A-Za-z]+)"\s*:', l))))
            if ks not in seen or len(l) < len(seen[ks]):
                seen[ks] = l
    lines = [v for _, v in sorted(seen.items()) if len(v) < 6000]
    os.makedirs(outdir, exist_ok=True)
    open(os.path.join(outdir, 'header.txt'), 'wb').write(hdr)
    open(os.path.join(outdir, 'corpus.txt'), 'wb').write(b'\n'.join(lines))
    keys = set()
    for l in lines:
        keys |= set(re.findall(rb'"([A-Za-z]+)"\s*:', l))
    print('%d records, %d distinct keys' % (len(lines), len(keys)))


def run(binary, path):
    r = subprocess.run([binary, path], capture_output=True, timeout=600)
    return r.returncode, (r.stdout + r.stderr).replace(path.encode(), b'<F>')


def compare(old, new, cases):
    bad = 0
    tmp = tempfile.NamedTemporaryFile(suffix='.ndjson', delete=False)
    tmp.close()
    for n, data in enumerate(cases):
        open(tmp.name, 'wb').write(data)
        a, b = run(old, tmp.name), run(new, tmp.name)
        if a != b:
            bad += 1
            print('MISMATCH case %d' % n)
            print('  old:', a)
            print('  new:', b)
            if bad > 10:
                break
        if (n + 1) % 2000 == 0:
            print('… %d cases, %d mismatches' % (n + 1, bad), flush=True)
    os.unlink(tmp.name)
    print('DONE %d cases, %d mismatches' % (n + 1, bad))
    return 1 if bad else 0


def rand_key(rnd):
    r = rnd.random()
    if r < 0.4:
        return rnd.choice(KEYS)
    if r < 0.8:
        k = rnd.choice(KEYS)
        p = rnd.randrange(len(k))
        return k[:p] + rnd.choice(LET) + k[p+1:]
    return ''.join(rnd.choice(LET) for _ in range(rnd.randrange(1, 12)))


def mutate(rnd, line):
    ks = key_spans(line)
    if ks and rnd.random() < 0.25:
        s, e = rnd.choice(ks)
        return line[:s+1] + rand_key(rnd).encode() + line[e:]
    if ks and rnd.random() < 0.5:
        s, e = rnd.choice(ks)
        p = rnd.randrange(s, e + 1)
    else:
        p = rnd.randrange(0, max(1, len(line)))
    op = rnd.randrange(3)
    if op == 0 and line:
        return line[:p] + bytes([rnd.choice(ALPH)]) + line[p+1:]
    if op == 1:
        return line[:p] + bytes([rnd.choice(ALPH)]) + line[p:]
    return line[:p] + line[p+1:]


def load(d):
    hdr = open(os.path.join(d, 'header.txt'), 'rb').read().strip()
    corpus = [l for l in open(os.path.join(d, 'corpus.txt'), 'rb').read()
              .split(b'\n') if l.strip()]
    return hdr, corpus


def main():
    mode = sys.argv[1]
    if mode == 'harvest':
        harvest(sys.argv[2])
        return 0
    old, new = sys.argv[2], sys.argv[3]
    if mode == 'keysweep':
        hdr, corpus = load(sys.argv[4])
        cases = []
        for li, line in enumerate(corpus):
            spans = key_spans(line)
            for (s, e) in spans:
                for k in KEYS:
                    cases.append(line[:s+1] + k.encode() + line[e:])
            if li % 3 == 0 and spans:
                s, e = spans[0]
                for k in KEYS:
                    vs = [k[:-1], k[1:], k + 'x', 'x' + k]
                    vs += [k[:p] + c + k[p+1:]
                           for p in range(len(k)) for c in 'azKe']
                    cases += [line[:s+1] + v.encode() + line[e:] for v in vs]
        return compare(old, new, (hdr + b'\n' + c + b'\n' for c in cases))
    n = int(sys.argv[4])
    rnd = random.Random(20260909)
    if mode == 'fuzz':
        hdr, corpus = load(sys.argv[5])

        def gen():
            for _ in range(n):
                yield hdr + b'\n' + mutate(rnd, rnd.choice(corpus)) + b'\n'
    else:
        streams = [open(f, 'rb').read().split(b'\n') for f in sys.argv[5:]]

        def gen():
            for _ in range(n):
                L = list(rnd.choice(streams))
                i = rnd.randrange(len(L))
                while not L[i].strip():
                    i = rnd.randrange(len(L))
                L[i] = mutate(rnd, L[i])
                yield b'\n'.join(L)
    return compare(old, new, gen())


if __name__ == '__main__':
    sys.exit(main())
