#!/usr/bin/env bash
# tests/unconsumed.sh — THE UNCONSUMED-DECLARATION LENS (ADVISORY).
#
# WHAT IT CHECKS.  Every `theorem`/`def` declared under
# `ConLeche/Model/Inductives/` and `ConLeche/Verify/Inductives/` whose
# name occurs NOWHERE in the tree's Lean CODE outside its own
# declaration.  Docstrings and comments do not count as consumers —
# they are stripped first, together with string literals — so a lemma
# that is only ever *mentioned* in prose reads as unconsumed here, which
# is exactly the finding.
#
# WHY.  A theorem nothing uses is a liability: it is proof effort that
# buys nothing, it drifts out of shape with the statements it was meant
# to serve, and — worst — it reads like progress.  This route has
# discovered the same thing by hand three times in one day
# (`nestedCtorsStaged_of_pins`' own docstring records one: "the law was
# proved and had no call site, and a premise with no call site is
# indistinguishable from a premise with no proof").  The existing gates
# do not see it: `tests/shake.sh` decides IMPORT lines and
# `tests/proofdeps.sh` decides what a proof TERM contains — neither asks
# whether a declaration has a consumer at all.
#
# IT IS ADVISORY.  It always exits 0 and it is wired into neither
# `tests/arena.sh` nor CI.  Not every hit is a defect: a named residual
# waiting for its producer, a capstone statement that is the deliverable,
# and an `@[simp]`/`@[grind]` lemma consumed by a tactic rather than by
# name are all legitimately consumer-free.  The list is a lens to read,
# not a verdict; `tests/unconsumed-allow.txt` (one name per line) mutes
# entries that have been read and accepted.
#
# HOW IT COUNTS.  Comments (`--`, nested `/- -/`, docstrings) and string
# literals are blanked by a small state machine, the rest of the tree is
# tokenised once into identifier components, and a declaration is
# unconsumed when the token count outside its own body is zero.  Because
# the corpus is tokenised on `.`, a dotted declaration `A.b` is looked up
# by its LAST component, so dot-notation uses (`x.b`) count — the bias is
# deliberately towards under-reporting.
set -u
cd "$(dirname "$0")/.."

python3 - <<'PY'
import re
import subprocess
from collections import Counter

SCOPE = ("ConLeche/Model/Inductives/", "ConLeche/Verify/Inductives/")
ALLOW = "tests/unconsumed-allow.txt"

IDENT = re.compile(r"[^\W\d][\w'!?]*", re.UNICODE)

# a top-level declaration's body ends at the next line that starts in
# column 0 with one of these (comments are already blanked, so a
# docstring cannot end a body early)
STOP = re.compile(
    r"^(?:@\[|theorem\b|def\b|lemma\b|abbrev\b|instance\b|structure\b|inductive\b"
    r"|class\b|example\b|axiom\b|opaque\b|end\b|namespace\b|section\b|variable\b"
    r"|open\b|universe\b|local\b|attribute\b|set_option\b|deriving\b|macro\b"
    r"|syntax\b|notation\b|elab\b|import\b|module\b|private\b|protected\b"
    r"|public\b|noncomputable\b|partial\b|unsafe\b|meta\b|mutual\b|where\b)")

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|public|noncomputable|partial|unsafe|meta|scoped)\s+)*"
    r"(theorem|def)\s+([^\s({\[:⦃⟨]+)")


def blank(src: str) -> str:
    """Replace comment and string-literal characters by spaces, keeping
    every newline (and therefore every line number) in place."""
    out = list(src)
    i, n, depth = 0, len(src), 0
    while i < n:
        c = src[i]
        if depth:                                   # inside /- ... -/
            if src.startswith("/-", i):
                depth += 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if src.startswith("-/", i):
                depth -= 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if c != "\n":
                out[i] = " "
            i += 1
            continue
        if src.startswith("/-", i):
            depth = 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if src.startswith("--", i):
            while i < n and src[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if c == '"':
            out[i] = " "
            i += 1
            while i < n:
                if src[i] == "\\":
                    out[i] = " "
                    if i + 1 < n and src[i + 1] != "\n":
                        out[i + 1] = " "
                    i += 2
                    continue
                if src[i] == '"':
                    out[i] = " "
                    i += 1
                    break
                if src[i] != "\n":
                    out[i] = " "
                i += 1
            continue
        if c == "'" and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] in "_'")):
            m = re.match(r"'(?:\\.|[^\\'])'", src[i:])
            if m:
                for k in range(i, i + m.end()):
                    out[k] = " "
                i += m.end()
                continue
        i += 1
    return "".join(out)


def main() -> int:
    files = subprocess.run(["git", "ls-files", "*.lean"], capture_output=True,
                           text=True, check=True).stdout.split()
    try:
        allow = {l.split("#", 1)[0].strip() for l in open(ALLOW)} - {""}
    except OSError:
        allow = set()

    total = Counter()       # identifier component -> occurrences, whole tree
    decls = []              # (file, line, name, lookup token, count in own body)

    for f in files:
        try:
            src = open(f, encoding="utf-8").read()
        except OSError:
            continue
        code = blank(src)
        total.update(IDENT.findall(code))
        if not f.startswith(SCOPE):
            continue
        lines = code.split("\n")
        starts = []
        for i, line in enumerate(lines):
            m = DECL.match(line)
            if m:
                starts.append((i, m.group(2)))
        for i, name in starts:
            j = i + 1
            while j < len(lines):
                if lines[j] and not lines[j][0].isspace() and STOP.match(lines[j]):
                    break
                j += 1
            tok = name.split(".")[-1]
            body = Counter(IDENT.findall("\n".join(lines[i:j])))
            decls.append((f, i + 1, name, tok, body[tok]))

    hits = [d for d in decls
            if total[d[3]] - d[4] == 0 and d[2] not in allow and d[3] not in allow]
    hits.sort(key=lambda d: (d[0], d[1]))
    scanned = len(decls)
    if hits:
        print(f"unconsumed (ADVISORY): {len(hits)} of {scanned} declarations under "
              f"{' / '.join(SCOPE)} have no consumer in Lean code")
        for f, ln, name, _, _ in hits:
            print(f"    {f}:{ln}: {name}")
    else:
        print(f"unconsumed (ADVISORY): none of {scanned} scoped declarations "
              f"is consumer-free")
    return 0


main()
PY
# advisory: a traceback above still reaches stderr, but the gate never fails
exit 0
