#!/usr/bin/env bash
# scripts/inlean-cached-diff.sh <old-master> <new-master> — a lane aid for an InLean sync
# (task #451, "How InLean follows master" in DESIGN.md).  NOT a gate.
#
# Prints the declarations changed between two master commits that InLean may have to
# follow: every declaration of `ConLeche/Cached/*`, and those of `ConLeche/Kernel/*` the
# binary runs (listed in `tests/plain-reach-allow.txt`, by name or as `module:`).  A
# declaration counts as changed when a changed line (added, removed or edited) falls
# inside it: between its header (`def`/`theorem`/`abbrev`/`instance`/`structure`/
# `inductive`/`class`, any modifiers) and the next header.  Names are qualified by the
# enclosing `namespace`s, best effort.  Lines before a file's first header are reported
# as `<preamble>`; a removed file reports its old declarations, an added file its new ones.
#
# Output: one line per declaration, `<tier> <file> <name>`, tier `cached` or `plain`.
set -euo pipefail
if [ $# -ne 2 ]; then
  echo "usage: $0 <old-master> <new-master>" >&2
  exit 2
fi
old=$1 new=$2
root=$(git rev-parse --show-toplevel)
cd "$root"
allow=tests/plain-reach-allow.txt

git diff --no-renames -U0 "$old" "$new" -- 'ConLeche/Cached/*.lean' \
    'ConLeche/Kernel/*.lean' |
python3 -I -c '
import re, subprocess, sys
old, new, allow = sys.argv[1], sys.argv[2], sys.argv[3]
names, mods = set(), set()
for l in open(allow):
    l = l.strip()
    if not l or l.startswith("#"): continue
    if l.startswith("module:"): mods.add(l[7:])
    else: names.add(l)
HDR = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|public|noncomputable|partial|unsafe|nonrec|meta)\s+)*"
                 r"(def|theorem|lemma|abbrev|instance|structure|inductive|class|opaque|axiom)\s+([^\s:({\[]+)?")
def show(rev, path):
    r = subprocess.run(["git", "show", f"{rev}:{path}"], capture_output=True, text=True)
    return r.stdout.splitlines() if r.returncode == 0 else []
def decls(lines):
    """For each line index, the qualified name of the declaration it lies in."""
    ns, owner, cur = [], [], "<preamble>"
    for l in lines:
        m = re.match(r"^\s*namespace\s+(\S+)", l)
        if m: ns.append(m.group(1))
        elif re.match(r"^\s*end\s+(\S+)\s*$", l) and ns:
            n = re.match(r"^\s*end\s+(\S+)", l).group(1)
            if ns[-1] == n: ns.pop()
        h = HDR.match(l)
        if h:
            short = h.group(2) or "<anonymous " + h.group(1) + ">"
            if short.startswith("_root_."): cur = short[7:]
            else: cur = ".".join(ns + [short]) if ns else short
        owner.append(cur)
    return owner
files = {}
cur = None
for l in sys.stdin:
    if l.startswith("diff --git"):
        cur = l.split()[2][2:]; files[cur] = ([], [])
    m = re.match(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@", l)
    if m and cur:
        a, an, b, bn = int(m[1]), int(m[2] or 1), int(m[3]), int(m[4] or 1)
        files[cur][0].extend(range(a, a + an)); files[cur][1].extend(range(b, b + bn))
out = []
for path, (olds, news) in files.items():
    tier = "cached" if path.startswith("ConLeche/Cached/") else "plain"
    mod = path[:-5].replace("/", ".")
    seen = set()
    for rev, ls in ((old, olds), (new, news)):
        lines = show(rev, path)
        own = decls(lines)
        for n in ls:
            if 1 <= n <= len(own): seen.add(own[n - 1])
    for d in sorted(seen):
        if tier == "plain" and mod not in mods and d not in names:
            continue
        out.append(f"{tier} {path} {d}")
print("\n".join(out))
' "$old" "$new" "$allow"
