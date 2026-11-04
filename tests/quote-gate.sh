#!/usr/bin/env bash
# tests/quote-gate.sh — THE DOCUMENT QUOTE GATE (task #302).
#
# WHY THIS EXISTS.  `README.md` and `OVERVIEW.md` do not only LINK the
# code (that is `tests/overview-links.sh`, the link gate beside this
# one); they also QUOTE it — a fenced ```lean block holding the
# statement of a theorem so the reader can see it without leaving the
# page.  A quote rots exactly the way a line anchor does, and more
# quietly: renaming a binder, adding a hypothesis or re-indenting a
# continuation line leaves the link pointing at perfectly valid lines
# while the block above it shows a statement the tree no longer has.
# Nothing in the build reads a markdown fence.  This gate does.
#
# WHY TEXTUAL AND NOT `#check`.  `tests/challenge.sh` compares two
# *elaborated* statements — `#check @name` under `pp.universes` /
# `pp.explicit` / `pp.proofs` — because there the question is whether
# two modules state the same proposition, and spelling is irrelevant.
# Here the question is the opposite one.  The documents quote SOURCE
# TEXT, for a human to read next to the prose, so what must be true is
# that the block IS the source: same binder names, same notation, same
# line breaks, same indentation.  `#check` normalises all of that away
# and would happily accept a quote that names `chunks` where the source
# now says `cs`, or that predates a `{}`→`()` binder change — a quote
# that is wrong for every reader and right for the elaborator.  So the
# comparison is textual, and the source is the truth.
#
# WHAT IT SCOPES.  Every fenced ```lean block in `$DOCS` whose first
# significant line starts with `theorem <name>` or `def <name>`, where
# the block may carry, ahead of that line, any number of `open … in`
# lines and `@[…]` attribute lines (the two prefixes a statement is
# actually written with).  A ```lean block that is not headed by a
# declaration — an example, a snippet, a signature sketch — is out of
# scope and is reported in the summary as skipped, so that adding one
# is a visible decision rather than a silent hole.
#
# WHAT IT COMPARES.  The block, against the declaration's HEADER as the
# source writes it:
#
#   * the header starts at the `theorem <name>` / `def <name>` line;
#   * it is extended BACKWARDS over the `open … in` and `@[…]` lines
#     that sit directly above the declaration, skipping a docstring
#     between them (the source's usual order is `open … in`, then the
#     `/-- … -/`, then the `theorem`; the docstring is never quoted);
#   * it ends where the STATEMENT ends: the first `:=` (or `where`)
#     that stands at bracket depth 0, exclusive — so the body, the
#     `by`, and a `:=` that lives inside the statement (a `let` inside
#     a `do` block, a default argument) are not part of the quote.
#
# The two texts are compared after stripping TRAILING whitespace from
# every line, and nothing else: indentation is significant, because the
# continuation indentation is what a reader copies.
#
# WHICH DECLARATION.  The name is resolved by its SHORT name across
# `ConLeche/**/*.lean` and `Main.lean` (a document quotes
# `theorem model_exists`, the tree declares `ConLeche.model_exists`
# inside a `namespace`).  If more than one file declares that short
# name — `no_False_declaration` is declared twice, in
# `ConLeche/MainTheorem.lean` and in its sorry'd Comparator twin
# `ConLeche/Challenge.lean` — the gate takes the LAST markdown link
# ABOVE the block whose target is one of the candidates, which is how
# the documents already say which one they mean (the README's
# `[ConLeche/MainTheorem.lean](./ConLeche/MainTheorem.lean)` a
# paragraph up).  Both link shapes count: a `blob/master/<path>` code
# link and a relative one.  If no link above the block names a
# candidate, the ambiguity is reported with the candidate list rather
# than guessed.
#
# NO `--update`.  The link gate has one because the cited TEXT is not
# derivable from the document; here it is: the source is the truth and
# the fix for a failure is to re-sync the quote in the document.  An
# `--update` would write the documents, which is the one thing a gate
# over a human-written README must not do on its own.  (Agents MAY
# edit a quoted code block to re-sync it — maintainer, 2026-09-13 —
# but that is an edit made after reading the diff, not a generated one.)
#
# NO BUILD REQUIRED.  A pure source-tree gate, like the link gate: it
# reads the documents and the quoted files and nothing else.
set -u
cd "$(dirname "$0")/.."

DOCS="README.md OVERVIEW.md"

case "${1:-}" in
  "") ;;
  *) echo "usage: tests/quote-gate.sh" >&2; exit 2 ;;
esac

for doc in $DOCS; do
  if [ ! -f "$doc" ]; then
    echo "quote-gate: FAIL — $doc not found" >&2
    exit 1
  fi
done

python3 - $DOCS <<'PY'
import os, re, sys, difflib

docs = sys.argv[1:]

# Any markdown destination that can name a source file: a `blob/master`
# link (the canonical code link) or a relative one (`./ConLeche/X.lean`).
DEST = re.compile(r'\]\(([^)\s]+)\)')
BLOB = re.compile(r'^https://github\.com/[^/\s]+/[^/\s]+/blob/master/(.+)$')
DECL = re.compile(r'^(theorem|def)\s+([^\s({\[:]+)')
OPEN_IN = re.compile(r'^open\b.*\bin$')
ATTR = re.compile(r'^@\[.*\]$')


def read(path):
    with open(path, encoding='utf-8') as f:
        lines = f.read().split('\n')
    if lines and lines[-1] == '':
        lines.pop()
    return lines


def sources():
    """Every source file a document may quote from, in a stable order."""
    out = []
    for root, dirs, files in os.walk('ConLeche'):
        dirs.sort()
        for f in sorted(files):
            if f.endswith('.lean'):
                out.append(os.path.join(root, f))
    if os.path.isfile('Main.lean'):
        out.append('Main.lean')
    return out


def statement_end(lines, start):
    """Index and column of the `:=`/`where` that ends the statement.

    Scans from the declaration line, tracking bracket depth so that a
    `:=` inside the statement (a `let` in a `do` block, a default
    argument) is not mistaken for the body's.  Returns (line, col) with
    the text BEFORE that token being the statement, or None.
    """
    depth = 0
    i = start
    while i < len(lines):
        line = lines[i]
        j = 0
        while j < len(line):
            c = line[j]
            if c == '"':                       # skip a string literal
                j += 1
                while j < len(line):
                    if line[j] == '\\':
                        j += 2
                        continue
                    if line[j] == '"':
                        break
                    j += 1
                j += 1
                continue
            if c == '-' and line.startswith('--', j):
                break                          # line comment: rest is prose
            if c in '([{':
                depth += 1
            elif c in ')]}':
                depth -= 1
            elif depth == 0 and line.startswith(':=', j):
                return (i, j)
            elif depth == 0 and line.startswith('where', j) and \
                    (j == 0 or not line[j-1].isalnum()) and \
                    not line[j+5:j+6].isalnum():
                return (i, j)
            j += 1
        # Bracket depth carries across lines; only the token search
        # restarts.  A declaration whose body is 200 lines away is not a
        # statement this gate can delimit, and says so rather than
        # scanning the rest of the file.
        i += 1
        if i - start > 200:
            return None
    return None


def header_of(path, name):
    """The source text of `name`'s statement in `path`, or None.

    Returns (text, first_line_number, last_line_number).
    """
    lines = read(path)
    for i, line in enumerate(lines):
        m = DECL.match(line)
        if not m or m.group(2) != name:
            continue
        end = statement_end(lines, i)
        if end is None:
            return ('!', i + 1, i + 1)
        e, col = end
        body = lines[i:e] + [lines[e][:col]]
        # Walk backwards over the prefixes the quote may carry.  A
        # docstring between them and the declaration is stepped over and
        # never quoted, so the reported span may contain lines the quote
        # does not show; the diff's own labels say which text is which.
        j = i - 1
        prefix = []
        first = i + 1
        while j >= 0:
            s = lines[j]
            if s.rstrip().endswith('-/'):      # a docstring: skipped, not quoted
                while j >= 0 and not lines[j].lstrip().startswith('/-'):
                    j -= 1
                j -= 1
                continue
            if ATTR.match(s) or OPEN_IN.match(s):
                prefix.insert(0, s)
                first = j + 1
                j -= 1
                continue
            break
        text = [l.rstrip() for l in prefix + body]
        while text and text[-1] == '':
            text.pop()
        return ('\n'.join(text), first, e + 1)
    return None


SRC = sources()
errors = []
checked = []
skipped = []

for doc in docs:
    lines = read(doc)
    i = 0
    while i < len(lines):
        if lines[i].strip() != '```lean':
            i += 1
            continue
        start = i
        i += 1
        block = []
        while i < len(lines) and lines[i].strip() != '```':
            block.append(lines[i])
            i += 1
        if i >= len(lines):
            errors.append(f"{doc}:{start+1}: unterminated ```lean block.")
            break
        i += 1

        # The block's significant head: skip `open … in` / `@[…]` lines.
        k = 0
        while k < len(block) and (OPEN_IN.match(block[k]) or ATTR.match(block[k])):
            k += 1
        m = DECL.match(block[k]) if k < len(block) else None
        if not m:
            skipped.append(f"{doc}:{start+1}")
            continue
        name = m.group(2)

        cands = [p for p in SRC if any(
            DECL.match(l) and DECL.match(l).group(2) == name for l in read(p))]
        if not cands:
            errors.append(
                f"{doc}:{start+1}: the quoted block declares `{name}`, which no\n"
                f"    file under ConLeche/ or Main.lean declares.")
            continue
        if len(cands) > 1:
            # Disambiguate by the LAST link above the block whose target
            # is one of the candidates — a code link or a relative one.
            near = None
            for l in lines[:start]:
                for dm in DEST.finditer(l):
                    bm = BLOB.match(dm.group(1))
                    dest = (bm.group(1) if bm else dm.group(1)).split('#', 1)[0]
                    if dest.startswith('./'):
                        dest = dest[2:]
                    if dest in cands:
                        near = dest
            if near is not None:
                cands = [near]
            else:
                errors.append(
                    f"{doc}:{start+1}: `{name}` is declared in several files and no\n"
                    f"    link above the block names one of them:\n"
                    f"    " + ", ".join(cands))
                continue
        path = cands[0]
        got = header_of(path, name)
        if got is None or got[0] == '!':
            errors.append(
                f"{doc}:{start+1}: cannot delimit `{name}`'s statement in {path} —\n"
                f"    no `:=` or `where` at bracket depth 0 after its declaration line.")
            continue
        src, a, b = got
        quoted = '\n'.join(l.rstrip() for l in block)
        while quoted.endswith('\n'):
            quoted = quoted[:-1]
        if quoted == src:
            checked.append(f"{name} ({doc} → {path}:L{a}-L{b})")
            continue
        diff = '\n'.join('    ' + l for l in difflib.unified_diff(
            src.split('\n'), quoted.split('\n'),
            fromfile=f"{path}:L{a}-L{b}", tofile=f"{doc}:{start+2}",
            lineterm=''))
        errors.append(
            f"the quoted statement of `{name}` in {doc} differs from {path}:L{a}-L{b}\n"
            f"{diff}")

if errors:
    sys.stderr.write("quote-gate: FAIL — %d quoted statement(s) out of sync:\n\n"
                     % len(errors))
    for e in errors:
        sys.stderr.write("  " + e + "\n\n")
    sys.stderr.write(
        "The SOURCE is the truth: `-` is the tree, `+` is the document.\n"
        "The fix is to re-sync the QUOTE — copy the statement out of the\n"
        "source file, from the `theorem`/`def` line (with its `open … in`\n"
        "prefix, without its docstring) through the text before the final\n"
        "`:=`, indentation included.  Editing a quoted code block of\n"
        "README.md/OVERVIEW.md to match the tree is allowed for agents;\n"
        "changing the prose around it is not.  There is no --update: a\n"
        "gate over a human-written document does not rewrite it.\n")
    sys.exit(1)

print("quote-gate: %d quoted statement(s) match the tree%s"
      % (len(checked),
         ("; %d non-declaration ```lean block(s) skipped (%s)"
          % (len(skipped), ", ".join(skipped))) if skipped else ""))
for c in checked:
    print("  " + c)
PY
