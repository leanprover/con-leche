#!/usr/bin/env bash
# whitepaper/links-gate.sh — THE WHITEPAPER LINK GATE (task #323).
#
# An independent copy of the idea of `tests/overview-links.sh`, for the
# whitepaper's sources.  The paper cites the real proof and its own
# Lean fragment by LINE RANGE, and line anchors are the most perishable
# documentation there is: one added `import` slides every anchor in a
# module, and a link can keep pointing at valid lines that no longer
# say what the prose claims.  So the cited lines are a committed
# artefact — `whitepaper/links-expected.txt` — and this gate diffs the
# tree against it.
#
# WHICH DOCUMENTS.  Every `whitepaper/**/*.typ` (outside `_build/`), in
# sorted order, then `whitepaper/README.md` if present.
#
# WHICH LINKS.  Two shapes, both meaning
# `https://github.com/<owner>/<repo>/blob/master/<path>#L<a>[-L<b>]`:
#
#   * the literal URL (in `link(...)`, in README.md);
#   * a call of lib.typ's macro, `src("<path>", <a>[, <b>])`, whose
#     path and numbers must therefore be literals.
#
# Lines of a `.typ` file that are `//` comments are skipped (lib.typ's
# usage examples are not citations).
#
# WHAT IT CHECKS.  Each link's lines are copied, numbered, under a
# `== <path>#L<a>-L<b>` header, grouped per document under a
# `>>> <document>` banner, and the text is diffed against the
# expectation.  Hence: moved lines fail the gate (update the anchor);
# changed lines fail the gate (re-read the paragraph that cites them).
# Hard errors, naming the link: a missing file, an anchor outside the
# file, a ref other than `master`.  A RELATIVE markdown link
# (`](./x)`) in README.md must point at an existing file.
#
# After checking that the prose still matches, regenerate with
#
#     whitepaper/links-gate.sh --update
#
# and commit the expectation with the change that moved the lines.
#
# NO BUILD REQUIRED: it reads the sources and the cited files, nothing
# else, so it runs in `tests/arena.sh` beside the other fences and in
# `.github/workflows/whitepaper.yml`.

set -u
cd "$(dirname "$0")/.." || exit 3

EXPECTED=whitepaper/links-expected.txt

update=0
case "${1:-}" in
  --update) update=1 ;;
  "") ;;
  *) echo "usage: whitepaper/links-gate.sh [--update]" >&2; exit 2 ;;
esac

# The documents, in a stable order: the .typ sources sorted by path,
# then README.md.  Adding a section file inserts its block in path
# order, which is where a reader of the expectation would look for it.
docs=$(find whitepaper -name '*.typ' -not -path 'whitepaper/_build/*' | LC_ALL=C sort)
if [ -f whitepaper/README.md ]; then docs="$docs whitepaper/README.md"; fi
if [ -z "$docs" ]; then
  echo "whitepaper-links: FAIL — no documents found under whitepaper/" >&2
  exit 1
fi

tmp=$(mktemp) || exit 3
trap 'rm -f "$tmp"' EXIT

# The extractor: reads the documents in order, walks the links in each
# in order, writes the segment text to $1 — or reports EVERY structural
# error it finds and exits 1.
if ! python3 - "$tmp" $docs <<'PY'
import re, sys, os

out, docs = sys.argv[1], sys.argv[2:]

# github.com/<owner>/<repo>/blob/<ref>/<path>#L<a>[-L<b>]; owner/repo
# matched loosely so a project rename does not need a script edit.
LINK = re.compile(
    r'https://github\.com/([^/\s)"]+)/([^/\s)"]+)/blob/([^/\s)"]+)/'
    r'([^)\s#"]+)#L(\d+)(?:-L(\d+))?')

# lib.typ's `src("<path>", <a>[, <b>])`.
SRC = re.compile(r'\bsrc\(\s*"([^"]+)"\s*,\s*(\d+)(?:\s*,\s*(\d+))?\s*\)')

# Any inline markdown destination, for the relative-target check.
DEST = re.compile(r'\]\(([^)\s]+)\)')

errors = []
blocks = []

def cite(doc, shown, ref, path, a, b):
    """Return the segment text for one link, or record an error."""
    if ref != 'master':
        errors.append(
            f"{doc}: {shown}\n    pins the ref `{ref}`; the document must link `master`.")
        return None
    a = int(a)
    b = int(b) if b is not None else a
    anchor = f"#L{a}" if b == a else f"#L{a}-L{b}"
    if not os.path.isfile(path):
        errors.append(f"{doc}: {shown}\n    file `{path}` does not exist.")
        return None
    with open(path, encoding='utf-8') as f:
        lines = f.read().split('\n')
    if lines and lines[-1] == '':
        lines.pop()
    n = len(lines)
    if a < 1 or b < a or b > n:
        errors.append(
            f"{doc}: {shown}\n    range L{a}-L{b} is outside `{path}` "
            f"(which has {n} lines).")
        return None
    body = ''.join(f"{i:6d}  {lines[i-1]}\n" for i in range(a, b + 1))
    return f"== {path}{anchor}\n{body}"

for doc in docs:
    with open(doc, encoding='utf-8') as f:
        text = f.read()
    is_typ = doc.endswith('.typ')
    if is_typ:
        # Drop `//` comment lines (keep their line count: nothing here
        # reports line numbers, but it keeps the scan simple).
        text = '\n'.join('' if ln.lstrip().startswith('//') else ln
                         for ln in text.split('\n'))

    # Walk both shapes in document order.
    found = []
    for m in LINK.finditer(text):
        owner, repo, ref, path, a, b = m.groups()
        found.append((m.start(), m.group(0), ref, path, a, b))
    if is_typ:
        for m in SRC.finditer(text):
            path, a, b = m.groups()
            found.append((m.start(), m.group(0), 'master', path, a, b))
    found.sort(key=lambda t: t[0])

    segments = []
    for _, shown, ref, path, a, b in found:
        seg = cite(doc, shown, ref, path, a, b)
        if seg is not None:
            segments.append(seg)

    if not is_typ:
        base = os.path.dirname(doc)
        for m in DEST.finditer(text):
            dest = m.group(1)
            if dest.startswith(('http://', 'https://', '#', 'mailto:')):
                continue
            target = dest.split('#', 1)[0]
            if target and not os.path.exists(os.path.join(base, target)):
                errors.append(
                    f"{doc}: [..]({dest})\n    target `{target}` does not exist "
                    f"(relative to {base}/).")

    blocks.append(f">>> {doc}\n\n" + "\n".join(segments))

if errors:
    sys.stderr.write("whitepaper-links: FAIL — %d bad link(s):\n" % len(errors))
    for e in errors:
        sys.stderr.write("  " + e + "\n")
    sys.exit(1)

header = (
    "# GENERATED by whitepaper/links-gate.sh --update — do not edit by hand.\n"
    "#\n"
    "# Every line-anchored link of the whitepaper's sources (literal URLs\n"
    "# and `src(\"path\", a, b)` calls), in document order, with the lines\n"
    "# it points at.  A diff here means a citation moved or its text\n"
    "# changed: re-read the paragraph that cites it, fix the link or the\n"
    "# prose, then regenerate.\n"
    "\n")

with open(out, 'w', encoding='utf-8') as f:
    f.write(header)
    f.write("\n".join(blocks))
    f.write("\n")
PY
then
  exit 1
fi

nlinks=$(grep -c '^== ' "$tmp")
nfiles=$(grep '^== ' "$tmp" | sed 's/#L.*//' | sort -u | wc -l)
ndocs=$(grep -c '^>>> ' "$tmp")

if [ "$update" = 1 ]; then
  if [ -f "$EXPECTED" ] && cmp -s "$tmp" "$EXPECTED"; then
    echo "whitepaper-links: $nlinks links, $nfiles files, $ndocs documents, expectation already current"
  else
    cp "$tmp" "$EXPECTED"
    echo "whitepaper-links: $nlinks links, $nfiles files, $ndocs documents, wrote $EXPECTED"
  fi
  exit 0
fi

if [ ! -f "$EXPECTED" ]; then
  echo "whitepaper-links: FAIL — $EXPECTED missing; run whitepaper/links-gate.sh --update" >&2
  exit 1
fi

if diff -u "$EXPECTED" "$tmp"; then
  echo "whitepaper-links: $nlinks links, $nfiles files, $ndocs documents, OK"
  exit 0
fi

# Name the documents whose section moved.
bad=""
for doc in $docs; do
  a=$(awk -v d="$doc" '/^>>> /{p=($2==d)} p' "$EXPECTED")
  b=$(awk -v d="$doc" '/^>>> /{p=($2==d)} p' "$tmp")
  if [ "$a" != "$b" ]; then bad="$bad $doc"; fi
done

cat >&2 <<MSG

whitepaper-links: FAIL — the cited lines are not what$bad
was written against.  \`-\` is the committed expectation, \`+\` the tree.

  * If a citation MOVED (the text is the same, the numbers shifted),
    update the line numbers in the document.
  * If the cited lines CHANGED, re-read the paragraph that cites them —
    the paper may now be stale.

Then regenerate:  whitepaper/links-gate.sh --update
MSG
exit 1
