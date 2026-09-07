#!/usr/bin/env python3
"""Resume slice of a lean4export 3.x ndjson stream: keep everything from
a cut point on, plus only what the kept suffix still needs from before it.

    resume_slice.py [--dry-run] [--report FILE] STREAM.ndjson CUT [OUT.ndjson]

`CUT` is either a 1-based *declaration record index* (the numbering
`_tmp/frontier3/decl_index.py` prints) or a declaration name; the cut
record itself is the first record of the kept suffix.  The output is a
valid `con-leche --pre` stream:

* every record at or after the cut is kept verbatim;
* of the records *before* the cut, exactly the transitive dependency
  closure reachable from the kept suffix is kept -- constants named in
  kept records' types/values/recursor rules, recursively.  Inductive
  blocks are single records, so they are kept whole.  The
  preprocessor's `_model` companions of every kept declaration are kept
  (the existing slicers' rule; `Kernel/Checker.lean`'s `directParts?`
  *requires* a block's companions to be absent to take the direct
  route, so dropping one would silently change the install route, and
  `projRewriteD` needs the block's `_model.proj_i.iota` artifacts).
  The pinned basis blocks (`Eq`, `Nat`, `PUnit`, `Empty`), every `quot`
  record and every `axiom` record are kept unconditionally -- `PUnit`
  gates the projection rewrite (`punitSeen`), the quotient basis needs
  the pinned `Eq`, and an axiom record is where a non-standard axiom's
  positive decline happens;
* every name (`in`) and level (`il`) record and the `meta` header are
  kept verbatim -- they are a few percent of the stream, so no name or
  level closure is needed;
* expression (`ie`) records keep their original ids; unreferenced ones
  are simply omitted, exactly as `_tmp/next-frontier/slice_fast.py`
  does.

Everything before the cut has a *known verdict* from the run that
reached the cut, so re-checking it buys nothing: this is the "resume
after a rung" tool.

=============================  SOUNDNESS CAVEAT  =============================
A RESUME SLICE HAS A SMALLER RESIDENT BASE THAN THE FULL STREAM.  The
parsed prefix is most of the checker's flat RSS (12.2 GiB of the 18.7
GiB ceiling on full Mathlib), so a *memory* blow-up that the full run
hits can fail to reproduce on the slice -- the finder's argument
against a prefix bisect (DESIGN, "The Mathlib frontier at 24.97 %",
sec. 2) applies here verbatim and in the same direction.  A slice can
only HIDE a failure, never invent one.

Use it for fast localisation and for re-checking after a fix.  NEVER as
the acceptance run: an accept on a resume slice is not an accept on the
stream.  Timings and peak RSS measured on a slice are likewise not the
stream's.

Two further fidelity notes:

* Tolerated-axiom taint (`sorryAx`).  Taint *propagation* survives the
  slice -- a kept declaration that used a skipped axiom still reaches
  the checker with its tainted dependency present, so it is still
  skipped -- but declarations dropped from the prefix contribute no
  skips, so the final `declined:` summary of a slice run can be
  strictly smaller than the full run's, and a full run that declines
  only because of a *dropped* prefix declaration shows up as an accept
  on the slice.
* String literals.  Reference extraction is regex-based over the raw
  JSON (as in every slicer here), so a `strVal` payload containing text
  like `"type":123` would be read as a reference.  That over-keeps; it
  never under-keeps.
============================================================================

Speed: two passes over the stream.  The prefix is scanned line by line
(the expression DAG is flattened into `array`s exactly as
`slice_fast.py` does); the suffix -- every record of which is kept --
is scanned with bulk `re.findall` over 256 MB chunks, which is ~7x
faster per byte and is all that is needed there, because the only thing
the suffix contributes is the set of *prefix* ids and names it
mentions.  The emit pass copies the whole suffix byte for byte and
filters only the prefix.

Why "every `ie` record after the cut is kept" is exact and not merely
conservative: lean4export emits an expression record the first time a
declaration's serialisation needs it, so every expression record
between two declaration records is reachable from the later one.
"""
import json
import re
import sys
import time
from array import array

CHUNK = 1 << 28  # 256 MB

DECL_KEYS = ("axiom", "def", "thm", "opaque", "quot", "inductive")
BASIS_TYPE_NAMES = {"Eq", "Nat", "PUnit", "Empty"}

IE_RE = re.compile(rb'^\{"ie":(\d+),')
NAME_STR_RE = re.compile(
    rb'\{"in":(\d+),"str":\{"pre":(\d+),"str":"((?:[^"\\]|\\.)*)"\}\}')
# the exporter writes object keys in alphabetical order, so the numeric
# form is `{"in":I,"num":{"i":K,"pre":P}}` -- `i` before `pre`
NAME_NUM_RE = re.compile(rb'\{"in":(\d+),"num":\{"i":(\d+),"pre":(\d+)\}\}')
# expression-node children *and* declaration-record roots (`type`,
# `value`).  Recursor-rule `rhs` slots come out of the JSON instead, so
# that a level record's `max`/`imax` payload can never be misread as an
# expression id.
EXPRREF_RE = re.compile(rb'"(?:fn|arg|body|type|value|struct)":(\d+)')
CONST_RE = re.compile(rb'"const":\{"name":(\d+),')
PROJ_RE = re.compile(rb'"typeName":(\d+)')
# the two in one scan, for the per-line prefix pass
CP_RE = re.compile(rb'"const":\{"name":(\d+),|"typeName":(\d+)')
# `{"ie":N,"app":{"arg":A,"fn":F}}` -- four out of five expression
# records are applications, and their shape is fixed (the exporter
# writes keys alphabetically), so they are parsed without a regex.  The
# guard is exact; anything else falls through to the generic path.
APP_HEAD = b'"app":{"arg":'
# a declaration record at the start of a line.  `(?m)^` costs 6x here
# (the engine re-anchors at every one of the ~8.4 M lines per 256 MB),
# so the newline is matched literally and a chunk's own first line --
# chunks are always line-aligned -- is tested separately.
DECL_LINE_RE = re.compile(
    rb'\n\{"(?:' + b"|".join(k.encode() for k in DECL_KEYS) + rb')":')
DECL_HEAD_RE = re.compile(
    rb'^\{"(?:' + b"|".join(k.encode() for k in DECL_KEYS) + rb')":')


def log(msg):
    print(f"[{time.strftime('%H:%M:%S')}] resume_slice: {msg}",
          file=sys.stderr, flush=True)


def unescape(seg):
    """A name segment, JSON-unescaped (fast path: no backslash)."""
    if b'\\' in seg:
        return json.loads(b'"' + seg + b'"')
    return seg.decode()


class Names:
    """The stream's name table: `pre` links plus the own segment."""

    def __init__(self):
        self.pre = array('i', [0])
        self.seg = [""]
        self.model = set()      # indices whose segment is `_model`
        self._res = {0: ""}

    def add(self, i, pre, seg):
        while len(self.seg) <= i:
            self.seg.append("")
            self.pre.append(0)
        self.pre[i] = pre
        self.seg[i] = seg
        if seg == "_model":
            self.model.add(i)

    def full(self, i):
        r = self._res.get(i)
        if r is not None:
            return r
        chain = []
        j = i
        while j not in self._res:
            chain.append(j)
            j = self.pre[j]
        s = self._res[j]
        for k in reversed(chain):
            s = (s + "." if s else "") + self.seg[k]
            self._res[k] = s
        return s

    def model_owner(self, i):
        """`T` if `i` is `T._model…`, else None (`slice_fast`'s
        `"._model" in n` rule, done on indices)."""
        model = self.model
        pre = self.pre
        j = i
        while j:
            if j in model:
                return pre[j]
            j = pre[j]
        return None


def parse_decl(rec):
    """(kind, declared name idxs, root expr ids, referenced name idxs)."""
    kind = next(iter(rec))
    v = rec[kind]
    if kind == "inductive":
        names, roots, refs = [], [], []
        for t in v["types"]:
            names.append(t["name"])
            roots.append(t["type"])
            refs.extend(t.get("all", ()))
            refs.extend(t.get("ctors", ()))
        for c in v["ctors"]:
            names.append(c["name"])
            roots.append(c["type"])
            refs.append(c["induct"])
        for r in v.get("recs", ()):
            names.append(r["name"])
            roots.append(r["type"])
            refs.extend(r.get("all", ()))
            for ru in r["rules"]:
                roots.append(ru["rhs"])
                refs.append(ru["ctor"])
        return kind, names, roots, refs
    if kind not in DECL_KEYS:
        sys.exit(f"unknown record kind {kind!r}")
    roots = [v["type"]]
    if "value" in v:
        roots.append(v["value"])
    return kind, [v["name"]], roots, []


class Scan:
    """Pass 1: the name table, every declaration record, the prefix
    expression DAG, and what the suffix refers back to."""

    def __init__(self, stream, cut):
        self.stream = stream
        self.nm = Names()
        self.d_names = []
        self.d_roots = []
        self.d_refs = []
        self.d_kind = []
        self.forced = []            # ordinals kept unconditionally
        self.decl_of_name = {}
        self.companions = {}        # owner name idx -> [decl ordinal]
        # prefix expression DAG, flattened (slice_fast's layout)
        self.kid_flat = array('i')
        self.kid_off = array('l', [0])
        self.cref = array('i')
        # what the suffix mentions
        self.seed_expr = set()
        self.seed_name = set()
        self.n_expr = 0
        self.n_bytes = 0
        self.cut_off = None
        self.cut_d = None
        self.boundary = None
        try:
            self.cut_idx = int(cut) - 1
            self.cut_name = None
            if self.cut_idx < 0:
                sys.exit("the cut record index is 1-based")
        except ValueError:
            self.cut_idx = None
            self.cut_name = cut
        self.run()

    # -- declaration bookkeeping -------------------------------------
    def note(self, rec):
        kind, names, roots, refs = parse_decl(rec)
        d = len(self.d_kind)
        self.d_names.append(names)
        self.d_roots.append(roots)
        self.d_refs.append(refs)
        self.d_kind.append(kind)
        setdefault = self.decl_of_name.setdefault
        owner_of = self.nm.model_owner
        comps = self.companions
        for n in names:
            setdefault(n, d)
            o = owner_of(n)
            if o is not None:
                comps.setdefault(o, []).append(d)
        if kind in ("axiom", "quot"):
            self.forced.append(d)
        elif kind == "inductive" and self.nm.full(names[0]) in BASIS_TYPE_NAMES:
            self.forced.append(d)
        return d

    # -- the two scanning modes --------------------------------------
    def bulk(self, buf):
        """A suffix chunk.  Every record here is kept, so all that is
        needed is the prefix ids and the names it mentions."""
        nm_add = self.nm.add
        for i, pre, seg in NAME_STR_RE.findall(buf):
            nm_add(int(i), int(pre), unescape(seg))
        for i, num, pre in NAME_NUM_RE.findall(buf):
            nm_add(int(i), int(pre), num.decode())
        self.n_expr += (buf.count(b'\n{"ie":')
                        + (1 if buf.startswith(b'{"ie":') else 0))
        b = self.boundary
        refs = list(map(int, EXPRREF_RE.findall(buf)))
        self.seed_expr.update([x for x in refs if x < b])
        self.seed_name.update(map(int, CONST_RE.findall(buf)))
        self.seed_name.update(map(int, PROJ_RE.findall(buf)))
        find = buf.find
        loads = json.loads
        starts = [m.start() + 1 for m in DECL_LINE_RE.finditer(buf)]
        if DECL_HEAD_RE.match(buf):
            starts.insert(0, 0)
        for s in starts:
            e = find(b'\n', s)
            d = self.note(loads(buf[s:] if e < 0 else buf[s:e]))
            self.forced.append(d)

    def prefix_lines(self, buf, base):
        """A prefix chunk, line by line.  Returns the byte offset just
        past the last line consumed; stops at the cut record."""
        nm = self.nm
        nm_add = nm.add
        kf_extend = self.kid_flat.extend
        ko_append = self.kid_off.append
        cr_append = self.cref.append
        kid_flat = self.kid_flat
        loads = json.loads
        off = base
        parts = buf.split(b'\n')
        if parts and parts[-1] == b'':
            parts.pop()
        for line in parts:
            head = line[:6]
            if head == b'{"ie":':
                m = IE_RE.match(line)
                if m is None:
                    sys.exit(f"unparsed expr record: {line[:120]!r}")
                eid = int(m.group(1))
                if eid != self.n_expr:
                    sys.exit(f"expression ids are not dense: saw {eid}, "
                             f"expected {self.n_expr}")
                self.n_expr = eid + 1
                p = m.end()
                if line[p:p + 13] == APP_HEAD and line[-2:] == b'}}':
                    j = line.index(b',', p + 13)
                    kf_extend((int(line[p + 13:j]), int(line[j + 6:-2])))
                    cr_append(-1)
                else:
                    kf_extend(map(int, EXPRREF_RE.findall(line, p)))
                    cm = CP_RE.search(line, p)
                    if cm is None:
                        cr_append(-1)
                    else:
                        g = cm.group(1)
                        cr_append(int(g if g is not None else cm.group(2)))
                ko_append(len(kid_flat))
            elif head == b'{"in":':
                m = NAME_STR_RE.match(line)
                if m is not None:
                    nm_add(int(m.group(1)), int(m.group(2)),
                           unescape(m.group(3)))
                else:
                    m = NAME_NUM_RE.match(line)
                    if m is None:
                        sys.exit(f"unparsed name record: {line[:120]!r}")
                    nm_add(int(m.group(1)), int(m.group(3)),
                           m.group(2).decode())
            elif head == b'{"il":' or line.startswith(b'{"meta"'):
                pass
            else:
                rec = loads(line)
                d = len(self.d_kind)
                if self.cut_idx is not None:
                    hit = (d == self.cut_idx)
                else:
                    hit = any(nm.full(x) == self.cut_name
                              for x in parse_decl(rec)[1])
                if hit:
                    self.cut_off = off
                    self.cut_d = d
                    self.boundary = self.n_expr
                    return off
                self.note(rec)
            off += len(line) + 1
        return off

    def run(self):
        base = 0
        with open(self.stream, 'rb') as f:
            while True:
                buf = f.read(CHUNK)
                if not buf:
                    break
                if not buf.endswith(b'\n'):
                    buf += f.readline()
                self.n_bytes += len(buf)
                if self.cut_off is None:
                    off = self.prefix_lines(buf, base)
                    if self.cut_off is not None:
                        self.bulk(buf[off - base:])
                else:
                    self.bulk(buf)
                base += len(buf)
        if self.cut_off is None:
            what = (f"record {self.cut_idx + 1}" if self.cut_name is None
                    else repr(self.cut_name))
            sys.exit(f"cut {what} not found ({len(self.d_kind)} declaration "
                     f"records in the stream)")


def mark(sc):
    """Pass 2 (in memory): the prefix closure of the kept suffix."""
    boundary = sc.boundary
    n_decl = len(sc.d_kind)
    seen = bytearray(boundary)
    kept_decl = bytearray(n_decl)
    kid_flat, kid_off, cref = sc.kid_flat, sc.kid_off, sc.cref
    d_roots, d_refs, d_names = sc.d_roots, sc.d_refs, sc.d_names
    companions, decl_of_name = sc.companions, sc.decl_of_name
    want = list(sc.seed_name)
    todo = []
    stack = []

    def walk(root):
        if root >= boundary or seen[root]:
            return
        push = stack.append
        pop = stack.pop
        push(root)
        while stack:
            e = pop()
            if e >= boundary or seen[e]:
                continue
            seen[e] = 1
            c = cref[e]
            if c >= 0:
                want.append(c)
            stack.extend(kid_flat[kid_off[e]:kid_off[e + 1]])

    def keep(d):
        if kept_decl[d]:
            return
        kept_decl[d] = 1
        for e in d_roots[d]:
            walk(e)
        want.extend(d_refs[d])
        for n in d_names[d]:
            cs = companions.get(n)
            if cs:
                todo.extend(cs)

    for d in range(sc.cut_d, n_decl):
        keep(d)
    for d in sc.forced:
        keep(d)
    for e in sc.seed_expr:
        walk(e)
    get = decl_of_name.get
    while want or todo:
        while todo:
            keep(todo.pop())
        while want:
            d = get(want.pop())
            if d is not None and not kept_decl[d]:
                keep(d)
    n_pre_kept = kept_decl[:sc.cut_d].count(1)
    n_expr_kept = seen.count(1)
    # how much of that the suffix asks for *directly* -- the rest is the
    # transitive closure through kept prefix declarations
    named = sc.seed_name
    direct = sum(1 for d in range(sc.cut_d)
                 if any(n in named for n in d_names[d]))
    log(f"pass 2: {n_pre_kept} of {sc.cut_d} prefix declaration records and "
        f"{n_expr_kept} of {boundary} prefix expression records kept "
        f"({direct} prefix records are named by the suffix directly; the "
        f"other {n_pre_kept - direct} come in transitively)")
    return kept_decl, seen


def emit(sc, kept_decl, kept_expr, out, dry_run):
    """Pass 3: filter the prefix, copy the suffix byte for byte."""
    boundary, cut_off = sc.boundary, sc.cut_off
    st = dict(ie_in=0, ie_out=0, decl_in=0, decl_out=0, other=0,
              b_in=0, b_out=0)
    fo = None if dry_run else open(out, 'wb')
    try:
        with open(sc.stream, 'rb') as f:
            left = cut_off
            eid = 0
            d = 0
            while left > 0:
                buf = f.read(min(CHUNK, left))
                left -= len(buf)
                if left > 0 and not buf.endswith(b'\n'):
                    extra = f.readline()
                    buf += extra
                    left -= len(extra)
                parts = buf.split(b'\n')
                if parts and parts[-1] == b'':
                    parts.pop()
                keep_lines = []
                app = keep_lines.append
                for line in parts:
                    n = len(line) + 1
                    st["b_in"] += n
                    head = line[:6]
                    if head == b'{"ie":':
                        st["ie_in"] += 1
                        k = kept_expr[eid]
                        eid += 1
                        if not k:
                            continue
                        st["ie_out"] += 1
                    elif (head == b'{"in":' or head == b'{"il":'
                          or line.startswith(b'{"meta"')):
                        st["other"] += 1
                    else:
                        st["decl_in"] += 1
                        k = kept_decl[d]
                        d += 1
                        if not k:
                            continue
                        st["decl_out"] += 1
                    st["b_out"] += n
                    app(line)
                if keep_lines and fo is not None:
                    fo.write(b'\n'.join(keep_lines) + b'\n')
            if eid != boundary:
                sys.exit(f"internal: emitted {eid} prefix expr records, "
                         f"expected {boundary}")
            while True:
                buf = f.read(CHUNK)
                if not buf:
                    break
                st["b_in"] += len(buf)
                st["b_out"] += len(buf)
                if fo is not None:
                    fo.write(buf)
    finally:
        if fo is not None:
            fo.close()
    st["ie_in"] += sc.n_expr - boundary
    st["ie_out"] += sc.n_expr - boundary
    st["decl_in"] += len(sc.d_kind) - sc.cut_d
    st["decl_out"] += len(sc.d_kind) - sc.cut_d
    return st


def report_text(sc, st, times, out, dry_run):
    tot_d = len(sc.d_kind)
    pre_d = sc.cut_d
    pre_kept = st["decl_out"] - (tot_d - pre_d)
    dropped_d = st["decl_in"] - st["decl_out"]
    pct = lambda a, b: 100.0 * a / b if b else 0.0
    L = []
    L.append(f"stream         {sc.stream}")
    L.append(f"cut            declaration record {pre_d + 1} of {tot_d} "
             f"({pct(pre_d + 1, tot_d):.3f} %)  "
             f"{sc.d_kind[pre_d]} {sc.nm.full(sc.d_names[pre_d][0])}")
    L.append(f"declarations   {tot_d} total | kept {st['decl_out']} | "
             f"dropped {dropped_d} ({pct(dropped_d, tot_d):.3f} % of stream)")
    L.append(f"  prefix       {pre_d} records | kept {pre_kept} "
             f"({pct(pre_kept, pre_d):.3f} %) | dropped {dropped_d} "
             f"({pct(dropped_d, pre_d):.3f} % of the prefix)")
    L.append(f"  suffix       {tot_d - pre_d} records | all kept")
    L.append(f"expr records   {st['ie_in']} total | kept {st['ie_out']} | "
             f"dropped {st['ie_in'] - st['ie_out']} "
             f"({pct(st['ie_in'] - st['ie_out'], st['ie_in']):.3f} %)")
    L.append(f"  prefix       {sc.boundary} records | "
             f"kept {st['ie_out'] - (sc.n_expr - sc.boundary)} | "
             f"dropped {st['ie_in'] - st['ie_out']}")
    L.append(f"names+levels   {st['other']} prefix records, all kept")
    L.append(f"bytes          {st['b_in']} total | kept {st['b_out']} "
             f"({pct(st['b_out'], st['b_in']):.3f} %) | "
             f"dropped {st['b_in'] - st['b_out']} "
             f"({pct(st['b_in'] - st['b_out'], st['b_in']):.3f} %)")
    L.append(f"timing         scan {times[0]:.1f} s | mark {times[1]:.1f} s | "
             f"{'count' if dry_run else 'emit'} {times[2]:.1f} s | "
             f"total {sum(times):.1f} s")
    L.append("output         " + ("(dry run: nothing written)" if dry_run
                                  else str(out)))
    return "\n".join(L)


def main(argv):
    dry_run = False
    report = None
    args = []
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--dry-run":
            dry_run = True
        elif a == "--report":
            i += 1
            report = argv[i]
        elif a in ("-h", "--help"):
            print(__doc__)
            return 0
        elif a.startswith("-"):
            sys.exit(f"unknown option {a}")
        else:
            args.append(a)
        i += 1
    if len(args) == 2 and dry_run:
        args.append(None)
    if len(args) != 3:
        sys.exit("usage: resume_slice.py [--dry-run] [--report FILE] "
                 "STREAM.ndjson CUT [OUT.ndjson]")
    stream, cut, out = args

    t0 = time.time()
    sc = Scan(stream, cut)
    t1 = time.time()
    log(f"pass 1: {sc.n_bytes} B, {len(sc.nm.seg)} names, "
        f"{len(sc.d_kind)} declaration records, {sc.n_expr} expression "
        f"records; cut at record {sc.cut_d + 1} (byte {sc.cut_off}), "
        f"expression boundary {sc.boundary}; the suffix refers back to "
        f"{len(sc.seed_expr)} prefix expression records and names "
        f"{len(sc.seed_name)} constants ({t1 - t0:.1f} s)")
    kept_decl, kept_expr = mark(sc)
    t2 = time.time()
    st = emit(sc, kept_decl, kept_expr, out, dry_run)
    t3 = time.time()
    text = report_text(sc, st, (t1 - t0, t2 - t1, t3 - t2), out, dry_run)
    print(text)
    if report:
        with open(report, "w") as rp:
            rp.write(text + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
