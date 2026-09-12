#!/usr/bin/env bash
# tests/overview-links.sh — THE DOCUMENT LINK GATE (task #216; README.md
# added at task #299).
#
# WHY THIS EXISTS.  `OVERVIEW.md` is a guided tour of the proof whose
# claims are anchored: nearly every paragraph cites a *line range* of a
# source file through a `blob/master/<path>#L<a>-L<b>` link.  `README.md`
# — the maintainer's, human-written — names the same code by name, and
# since task #299 those names are links of the same shape.  Line
# anchors are the most perishable kind of documentation there is —
# inserting one `import` at the top of a module silently slides every
# anchor into it by one, and nothing in the build notices.  Worse, a
# link can keep pointing at valid lines that no longer say what the
# prose claims, which no existence check would catch.
#
# WHICH DOCUMENTS.  `$DOCS` below, in that order; the gate's name is
# historical (it predates README.md joining) and is kept because the
# expectation file, the output prefix and every DESIGN record cite it.
#
# WHAT IT CHECKS.  The gate does not try to decide whether the prose is
# true; it makes the *cited text* a committed artefact.  It extracts
# every `blob/master` link from each document in document order, copies
# the linked lines (with their line numbers) into one text under a
# `>>> <document>` banner per document, and diffs that against
# `tests/overview-links-expected.txt`.  Hence:
#
#   * moving the linked lines changes the line numbers in the text and
#     fails the gate — the reminder to update the link;
#   * editing the linked lines changes the text and fails the gate —
#     the reminder to re-read the paragraph that cites them, because
#     the document may now be stale in a way no tool can see;
#   * deleting the file, or shrinking it past the anchor, is a hard
#     error naming the link.
#
# The failure names the document whose citations moved.  It is never
# "you broke the docs, restore them": it is "the citation moved, look
# at what cites it".  After checking that the prose still matches,
# regenerate with
#
#     tests/overview-links.sh --update
#
# and commit the expectation with the change that moved the lines.
#
# README.md IS LINK-ONLY FOR AGENTS.  It is the one human-written file
# in the tree; an agent may turn an existing code name into a link and
# fix a link that rotted, and may change no other character.
#
# WHAT IS AN ERROR RATHER THAN A DIFF.  A link that pins a commit —
# `blob/<sha>/…` — is rejected outright: the documents must track
# `master`, or the gate would be pinning a snapshot and the tour would
# quietly drift from the tree it describes.  A RELATIVE link (`./PERF.md`,
# `./bridge/lean4lean-model`) is not line-anchored and has no cited text
# to pin, but its target must exist — one `os.path.exists`, which is what
# catches a renamed or deleted file behind a whole-file mention.  Links
# that are neither (external URLs, anchors within the document) are
# ignored; they are not this gate's business.
#
# WHAT IT DOES NOT CHECK.  Prose-only relative mentions (`tests/…`,
# directory names in the module map) are not link-extracted; they were
# audited once at task #216 and are cheap to re-audit by hand.  The gate
# also says nothing about links in `DESIGN.md`.
#
# NO BUILD REQUIRED.  This is a pure source-tree gate: it reads the
# documents and the cited files and nothing else, so it costs
# milliseconds and runs in `tests/arena.sh` beside the other fences.

set -u
cd "$(dirname "$0")/.."

# The documents, in the order their sections appear in the expectation.
# OVERVIEW.md stays first, so that adding a document appends a section
# rather than renumbering the file.
DOCS="OVERVIEW.md README.md"
EXPECTED=tests/overview-links-expected.txt

update=0
case "${1:-}" in
  --update) update=1 ;;
  "") ;;
  *) echo "usage: tests/overview-links.sh [--update]" >&2; exit 2 ;;
esac

for doc in $DOCS; do
  if [ ! -f "$doc" ]; then
    echo "overview-links: FAIL — $doc not found" >&2
    exit 1
  fi
done

tmp=$(mktemp) || exit 3
trap 'rm -f "$tmp"' EXIT

# The extractor.  Reads the documents in order, walks the links in each
# in order, and writes the segment text to $1 (or reports EVERY
# structural error it finds — a run that renames a module should see all
# its dead links at once, not one per invocation — and exits 1).
if ! python3 - "$tmp" $DOCS <<'PY'
import re, sys, os

out, docs = sys.argv[1], sys.argv[2:]

# github.com/<owner>/<repo>/blob/<ref>/<path>#L<a>[-L<b>]
#
# The owner/repo are matched loosely on purpose: the project has been
# renamed before and the gate should survive the next rename without a
# script edit.  The <ref> is what matters, and it must be `master`.
LINK = re.compile(
    r'https://github\.com/([^/\s)]+)/([^/\s)]+)/blob/([^/\s)]+)/'
    r'([^)\s#]+)#L(\d+)(?:-L(\d+))?')

# Any inline markdown destination, for the relative-target check below.
DEST = re.compile(r'\]\(([^)\s]+)\)')

errors = []
blocks = []

for doc in docs:
    with open(doc, encoding='utf-8') as f:
        text = f.read()

    segments = []
    for m in LINK.finditer(text):
        owner, repo, ref, path, a, b = m.groups()
        link = m.group(0)
        if ref != 'master':
            errors.append(
                f"{doc}: {link}\n    pins the ref `{ref}`; the document must link `master`.")
            continue
        a = int(a)
        b = int(b) if b is not None else a
        anchor = f"#L{a}" if b == a else f"#L{a}-L{b}"
        if not os.path.isfile(path):
            errors.append(f"{doc}: {link}\n    file `{path}` does not exist.")
            continue
        with open(path, encoding='utf-8') as f:
            lines = f.read().split('\n')
        # A trailing newline yields a final empty element; it is not a line.
        if lines and lines[-1] == '':
            lines.pop()
        n = len(lines)
        if a < 1 or b < a or b > n:
            errors.append(
                f"{doc}: {link}\n    range L{a}-L{b} is outside `{path}` "
                f"(which has {n} lines).")
            continue
        body = ''.join(f"{i:6d}  {lines[i-1]}\n" for i in range(a, b + 1))
        segments.append(f"== {path}{anchor}\n{body}")

    # Relative links: no cited text to pin, but the target must exist.
    # A whole-file mention (`./PERF.md`, `./bridge/lean4lean-model`) is
    # the one link shape that rots into a 404 with nothing else noticing.
    for m in DEST.finditer(text):
        dest = m.group(1)
        if dest.startswith(('http://', 'https://', '#', 'mailto:')):
            continue
        target = dest.split('#', 1)[0]
        if target and not os.path.exists(target):
            errors.append(f"{doc}: [..]({dest})\n    target `{target}` does not exist.")

    blocks.append(f">>> {doc}\n\n" + "\n".join(segments))

if errors:
    sys.stderr.write("overview-links: FAIL — %d bad link(s):\n" % len(errors))
    for e in errors:
        sys.stderr.write("  " + e + "\n")
    sys.exit(1)

header = (
    "# GENERATED by tests/overview-links.sh --update — do not edit by hand.\n"
    "#\n"
    "# Every line-anchored link of the gated documents, in document order,\n"
    "# with the lines it points at.  A diff here means a citation moved or\n"
    "# its text changed: re-read the paragraph that cites it, fix the link\n"
    "# or the prose, then regenerate.\n"
    "\n")

with open(out, 'w', encoding='utf-8') as f:
    f.write(header)
    f.write("\n".join(blocks))
    f.write("\n")
PY
then
  exit 1
fi

# The summary counts, read back off the generated text: the header
# lines ARE the link list, so no second channel is needed.
nlinks=$(grep -c '^== ' "$tmp")
nfiles=$(grep '^== ' "$tmp" | sed 's/#L.*//' | sort -u | wc -l)
ndocs=$(grep -c '^>>> ' "$tmp")

if [ "$update" = 1 ]; then
  if [ -f "$EXPECTED" ] && cmp -s "$tmp" "$EXPECTED"; then
    echo "overview-links: $nlinks links, $nfiles files, $ndocs documents, expectation already current"
  else
    cp "$tmp" "$EXPECTED"
    echo "overview-links: $nlinks links, $nfiles files, $ndocs documents, wrote $EXPECTED"
  fi
  exit 0
fi

if [ ! -f "$EXPECTED" ]; then
  echo "overview-links: FAIL — $EXPECTED missing; run tests/overview-links.sh --update" >&2
  exit 1
fi

if diff -u "$EXPECTED" "$tmp"; then
  echo "overview-links: $nlinks links, $nfiles files, $ndocs documents, OK"
  exit 0
fi

# Name the documents whose section moved: the banner splits both texts,
# and a section that compares equal is not the one to go re-read.
bad=""
for doc in $DOCS; do
  a=$(awk -v d="$doc" '/^>>> /{p=($2==d)} p' "$EXPECTED")
  b=$(awk -v d="$doc" '/^>>> /{p=($2==d)} p' "$tmp")
  if [ "$a" != "$b" ]; then bad="$bad $doc"; fi
done

cat >&2 <<MSG

overview-links: FAIL — the cited lines are not what$bad
was written against.  \`-\` is the committed expectation, \`+\` the tree.

  * If a citation MOVED (the text is the same, the numbers shifted),
    update the \`#L<a>-L<b>\` anchor in the document.
  * If the cited lines CHANGED, re-read the paragraph that cites them —
    the document may now be stale.  (README.md is human-written: an
    agent may repoint a link and change nothing else.)

Then regenerate:  tests/overview-links.sh --update
MSG
exit 1
