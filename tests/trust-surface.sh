#!/usr/bin/env bash
# tests/trust-surface.sh — THE TRUST-SURFACE GATE (2026-09-06, external
# review §5.6).
#
# WHY THIS EXISTS.  `tests/layering.sh` fences one direction of trust:
# the implementation may not import the theory.  This gate fences the
# other: **no compiler escape may appear outside the files that are
# knowingly part of the trusted computing base.**
#
# The escapes matter because they are invisible to `#print axioms`.  A
# theorem can stand at exactly `[propext, Classical.choice, Quot.sound]`
# (`tests/Axioms.lean` pins that) and still be about a function whose
# *compiled* behaviour was swapped out underneath it by
# `@[implemented_by]`, or read off a `@[computed_field]` word, or
# decided by `native_decide` (which would show up as `Lean.ofReduceBool`,
# but only if the axiom pin is looked at — which is why the two gates
# are complementary, not redundant).  An escape is therefore a TCB
# entry: it is admissible only where someone has written down why.
#
# WHAT IT SCANS.  Every `*.lean` in `ConLeche/`, `tests/`, `scripts/` and
# the three top-level roots (`Main`, `ConLeche`, `PinDump`; the fourth,
# `ConLechePreprocess`, went with the preprocessor at task #207), with
# block comments, line comments and string literals
# removed first — so the checker's own *data* (the `Name` literals
# `"sorryAx"`, `"ofReduceBool"`, the `"unsafe axiom"` rejection messages
# in `Frontend/ExportC.lean`) is not mistaken for an escape, and neither
# is the prose that documents the escapes.
#
# THE BLANKING IS A LEXER, NOT A REGEX (task #224).  It used to be four
# `re.sub`s, and the string one — `"(?:\\.|[^"\\])*"` — could not cross a
# backslash-NEWLINE, which is Lean's *string gap*
# (`"…\` NEWLINE `  …"`, ~90 of them in this tree).  A gap-carrying
# literal therefore did not match at all, quote parity flipped for the
# rest of the file, and from there on string CONTENT was scanned as
# code — the #213 lane saw its own error message's word `axiom`
# reported as a bare `axiom` declaration — while real code was scanned
# as string, which is the direction that matters: an escape could hide
# there unseen.  `code_only` is now a one-pass state machine
# (`scan_code` / `scan_string` / `scan_block_comment`) covering
#   * line comments `--`, and NESTED block comments `/- … /- … -/ … -/`
#     (so `/-!` module docs and `/--` doc comments too);
#   * string literals with every escape, INCLUDING the gap
#     (`\` NEWLINE, then the continuation line's leading blanks);
#   * INTERPOLATION: a `{…}` segment of a string is Lean source, so it
#     is left as CODE and an escape inside one is reported.  A `{` is
#     read as an interpolation only when a matching `}` closes it ON
#     THE SAME LINE (every interpolation in this tree is single-line,
#     and Lean's own `s!` idiom is); otherwise it is literal content.
#     That bound is what keeps a stray brace in a plain string from
#     desynchronising anything beyond its own line — and the scan is
#     speculative, restoring the blanking if the segment does not close.
#     The form is scanned in EVERY string, not just `s!"…"`/`m!"…"`,
#     because the prefix is not lexically decidable (`throwError "…{e}…"`
#     interpolates too); over-reading a literal `{b}` in a plain string
#     can only ever make the gate report MORE, which is loud and
#     fixable, never less;
#   * raw strings `r"…"`, `r#"…"#`, `r##"…"##` (no escapes inside);
#   * character literals `'x'`, `'\n'`, `'"'`, `'\''` — a `'` that
#     continues an identifier (`foo'`) is not one.
# Anything left unterminated at end of file (string, block comment) is a
# hard error, so a desynchronisation can never again be silent.
#
# The lexer has a FIXTURE and a SELF-TEST that the ordinary run performs:
# `tests/trust-surface/lexer.lean` exercises every form above and names,
# in trailing `EXPECT:` comment markers, exactly the lines the gate must
# report; `--selftest` runs that check alone.
#
# NOT SCANNED: `tests/e2e/src/*.lean` and `tests/trust-surface/*.lean`.
# The former are fixture *inputs* — the Lean sources that get exported
# into the streams the checker must REJECT — so they deliberately
# contain the very constructs this gate hunts
# (`tests/e2e/src/sorry_use.lean` is a `sorry`, by design).  The latter
# is the lexer fixture, which contains the same constructs for the same
# reason.  Neither is part of con-leche's own build.
#
# THE ALLOWLIST, and the justification for every entry (file → the
# tokens tolerated there).  A token in an allowlisted file that is not
# on its own list fails just as loudly as one in a bare file.
#
#   ConLeche/Kernel/Expr.lean          computed_field
#       The packed `@[computed_field] data` (hash / bvar bound / fvar
#       bound / …) and `Level.hashData` — the user's standing ruling,
#       *"Adopt computed_fields.  It's a compiler feature, we trust the
#       compiler"* (2026-09-04); the census that argues it is
#       `ConLeche/Cached/ExprNodes.lean`'s header.  Same escape class
#       `Lean.Expr` itself lives on.  The expression equality is NOT an
#       escape: `Expr.beq` goes through `@[csimp]` + `withPtrEq` /
#       `withPtrAddr` with the memoised descent PROVED equal to
#       `decide (a = b)` (`Expr.beqMemo_eq`), the same way the names
#       and levels below do — so the file tolerates no `unsafe`, no
#       `ptrAddrUnsafe` and no `implemented_by`.
#
#   ConLeche/Kernel/Name.lean          computed_field
#       A cached hash only (`Name.hashData`), exactly as `Lean.Name`'s.
#       `Level.hashData` is the same escape and lives in `Expr.lean`
#       above, which is why `ConLeche/Kernel/Level.lean` needs no entry.
#       Pointer equality is NOT an escape on either: it goes through
#       `@[csimp]` + `withPtrEq` with the redundancy proved
#       (`Name.beqPtr_eq`), per the user's 2026-09-05 ruling *"do not
#       use `implemented_by`"*.
#
#   ConLeche/Challenge.lean            sorry
#       THE PALOMAR CHALLENGE STATEMENT (task #183).  This file is the
#       *challenge* half of the Comparator pair (`comparator.json`): the
#       small readable statement of `ConLeche.no_proof_of_False` that a
#       reader audits, with `sorry` where the proof goes.  The `sorry`
#       is the whole point of the file — Comparator's contract is that
#       the challenge states the theorem and the *solution*
#       (`ConLeche/MainTheorem.lean`) proves it — and it is harmless
#       because the module is a TCB dead end: nothing in the tree
#       imports it, it roots its own `lean_lib` (`ConLecheChallenge`), and
#       that library is not in `defaultTargets`, so `lake build` never
#       builds it and no shipped or proved declaration can reach the
#       `sorryAx` it introduces.  A `sorry` anywhere else still fails
#       this gate.
#
#   ConLeche/Kernel/BasisGen.lean      unsafe, implemented_by
#       ELABORATOR-ONLY.  `#annotate_basis` / `#annotate_pins` run the
#       checker's own annotation pass at elaboration time through
#       `unsafe evalTerm` and splice the resulting literals.  Nothing
#       here is in the binary; the spliced literals are ordinary data
#       the proofs consume.
#
#   Main.lean                          unsafe
#       THE PERSISTENT MARK AT THE PHASE BOUNDARY.  Two term-level
#       `unsafe Runtime.markPersistent` calls in `checkDeclsIO`, taken
#       once at the phase boundary at every worker count, on the
#       installed `FEnv` and the pending-check array.  It is the same escape
#       `Lean.Environment.finalizeImport` uses for the same call, and
#       it is `unsafe` for one reason only: a marked closure is never
#       freed, and this process exits right after.  Nothing else about
#       it can be observed.  The graph is READ-ONLY from the boundary
#       on — every recorded check reads a prefix view of it from a
#       fresh memo state and writes nothing back — the call is the
#       IDENTITY on the value, and its result is DISCARDED, so the
#       `InstalledEnv` the driver goes on to use is the one it already
#       had and no verdict, and no step of the proof that `checkDecls`
#       returns that environment, can turn on whether the mark
#       happened.  `--no-mark-persistent` turns it off, and the output
#       is identical either way.  No `implemented_by` and no
#       `computed_field` is tolerated in this file.
#
# WHAT IS DELIBERATELY *NOT* ALLOWLISTED, and used to be:
# `ConLeche/SetTheory/Derive/*`.  Twenty `@[implemented_by …] … unsafeCast
# ()` stubs gave the noncomputable model operators compiled garbage so
# that they could be *mentioned* in computable definitions.  Nothing
# needed that (the operators were already `noncomputable def`s, and the
# implementation may not even import them — layering.sh), so they were
# deleted on 2026-09-06 rather than allowlisted.  This gate is what
# stops them growing back.
#
# Usage: tests/trust-surface.sh [--list|--selftest]
#   --list      print every scanned occurrence, allowlisted or not — the
#               census, for updating this header.
#   --selftest  run only the lexer self-test against
#               `tests/trust-surface/lexer.lean` (the ordinary run does
#               it first, then the scan).
set -u
cd "$(dirname "$0")/.."
exec python3 - "$@" <<'PYEOF'
import os, re, sys

# --------------------------------------------------------------- the
# tokens.  Each is a compiler escape that `#print axioms` cannot see.
TOKENS = {
    'unsafe':         re.compile(r'\bunsafe\b'),
    'unsafeCast':     re.compile(r'\bunsafeCast\b'),
    'ptrAddrUnsafe':  re.compile(r'\bptrAddrUnsafe\b'),
    'implemented_by': re.compile(r'\bimplemented_by\b'),
    'computed_field': re.compile(r'\bcomputed_field\b'),
    'native_decide':  re.compile(r'\bnative_decide\b'),
    # bare `ofReduceBool`/`ofReduceNat`: the meta-logic's compiler-trust
    # axioms.  The checker's own name constants (`ofReduceBoolName`,
    # `ofReduceBoolA`) are longer identifiers and do not match.
    'ofReduceBool':   re.compile(r'\bofReduce(?:Bool|Nat)\b'),
    'sorry':          re.compile(r'\bsorry\b'),
    'lcProof':        re.compile(r'\blcProof\b'),
    'extern':         re.compile(r'@\[[^\]]*\bextern\b'),
    'axiom':          re.compile(r'^\s*axiom\s', re.M),
}

ALLOW = {
    'Main.lean':                     {'unsafe'},
    'ConLeche/Challenge.lean':       {'sorry'},
    'ConLeche/Kernel/Expr.lean':     {'computed_field'},
    'ConLeche/Kernel/Name.lean':     {'computed_field'},
    'ConLeche/Kernel/BasisGen.lean': {'unsafe', 'implemented_by'},
}

# NOT SCANNED (see the header): fixture *inputs* that deliberately
# contain what the checker must reject, and the lexer's own fixture.
SKIP_DIRS = ('tests/e2e/src/', 'tests/trust-surface/')

ROOTS = ('Main.lean', 'ConLeche.lean', 'PinDump.lean')

LEXER_FIXTURE = 'tests/trust-surface/lexer.lean'

def sources():
    out = []
    for top in ('ConLeche', 'tests', 'scripts'):
        for dp, dirs, fs in os.walk(top):
            dirs[:] = [d for d in dirs if d != '.lake']
            for f in sorted(fs):
                if f.endswith('.lean'):
                    rel = os.path.join(dp, f)
                    if not rel.startswith(SKIP_DIRS):
                        out.append(rel)
    out += [r for r in ROOTS if os.path.exists(r)]
    return sorted(out)

# ------------------------------------------------------- the LEXER.
# `code_only` blanks every comment and every string literal, in one
# pass, keeping line AND column structure so reported line numbers and
# the echoed text stay true.  See the header for the forms covered and
# for why the regex it replaced was unsound.

class LexError(Exception):
    pass

# a character that may CONTINUE a Lean identifier — used to tell a
# raw-string prefix `r"` from the `r` that ends `myr`, and a character
# literal `'x'` from the prime in `foo'`.
_IDENT_TAIL = re.compile(r"[0-9A-Za-z_'!?À-￿]")
# `'x'`, `'\n'`, `'\''`, `'"'`, `'\x41'`, `'e'`
_CHARLIT = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^'\\\n])'")
# `r"`, `r#"`, `r##"` ...
_RAWSTR = re.compile(r'r(#*)"')

def code_only(src, path='<input>'):
    out = list(src)
    n = len(src)

    def blank(a, b):
        for k in range(a, b):
            if out[k] != '\n':
                out[k] = ' '

    def die(pos, msg):
        raise LexError(f'{path}:{src.count(chr(10), 0, pos) + 1}: {msg}')

    def ident_before(i):
        return i > 0 and _IDENT_TAIL.match(src[i - 1]) is not None

    def scan_block_comment(i, limit):
        """i is at `/-`.  Returns the index after the matching `-/`."""
        start, depth = i, 0
        while i < limit:
            if src.startswith('/-', i):
                depth += 1
                blank(i, i + 2); i += 2
            elif src.startswith('-/', i):
                depth -= 1
                blank(i, i + 2); i += 2
                if depth == 0:
                    return i
            else:
                blank(i, i + 1); i += 1
        die(start, 'unterminated block comment')

    def scan_raw_string(m, limit):
        """m matched `_RAWSTR`.  A raw string has no escapes at all; it
        ends at the quote followed by as many `#` as opened it."""
        close = '"' + m.group(1)
        j = src.find(close, m.end(), limit)
        if j < 0:
            die(m.start(), 'unterminated raw string literal')
        end = j + len(close)
        blank(m.start(), end)
        return end

    def scan_string(i, limit):
        """i is just after the opening `"`.  Returns the index after the
        closing `"`.  Blanks the literal text; a `{...}` interpolation
        segment is left as code."""
        start = i
        while i < limit:
            c = src[i]
            if c == '\\':
                if i + 1 >= limit:
                    die(i, 'backslash at end of input inside a string literal')
                if src[i + 1] == '\n':
                    # THE STRING GAP: `\` NEWLINE, then the continuation
                    # line's leading blanks, are not part of the value.
                    j = i + 2
                    while j < limit and src[j] in ' \t':
                        j += 1
                    blank(i, j); i = j
                else:
                    blank(i, i + 2); i += 2
                continue
            if c == '"':
                blank(i, i + 1)
                return i + 1
            if c == '{':
                # An interpolation `{...}`, but only if it closes on this
                # line (see the header); the attempt is speculative.
                eol = src.find('\n', i)
                stop = limit if eol < 0 else min(limit, eol)
                saved = out[i:]
                try:
                    j = scan_code(i + 1, stop, stop_brace=True)
                except LexError:
                    j = stop
                if j < stop and src[j] == '}':
                    blank(i, i + 1); blank(j, j + 1)
                    i = j + 1
                    continue
                out[i:] = saved          # not an interpolation after all
            blank(i, i + 1); i += 1
        die(start, 'unterminated string literal')

    def scan_code(i, limit, stop_brace=False):
        """Scan Lean source, blanking comments and string literals.
        With `stop_brace`, stop at the first unmatched `}` and return
        its index (the code inside a `{...}` interpolation)."""
        depth = 0
        while i < limit:
            c = src[i]
            if c == '/' and src.startswith('/-', i):
                i = scan_block_comment(i, limit)
                continue
            if c == '-' and src.startswith('--', i):
                j = src.find('\n', i)
                if j < 0 or j > limit:
                    j = limit
                blank(i, j); i = j
                continue
            if c == '"':
                blank(i, i + 1)
                i = scan_string(i + 1, limit)
                continue
            if c == 'r' and not ident_before(i):
                m = _RAWSTR.match(src, i, limit)
                if m:
                    i = scan_raw_string(m, limit)
                    continue
            if c == "'" and not ident_before(i):
                m = _CHARLIT.match(src, i, limit)
                if m:
                    blank(i, m.end()); i = m.end()
                    continue
            if stop_brace:
                if c == '{':
                    depth += 1
                elif c == '}':
                    if depth == 0:
                        return i
                    depth -= 1
            i += 1
        return i

    scan_code(0, n)
    return ''.join(out)

def scan_file(rel):
    """The (line, token, text) occurrences the gate sees in one file."""
    with open(rel, encoding='utf-8') as fh:
        raw = fh.read()
    hits = []
    for i, line in enumerate(code_only(raw, rel).split('\n'), 1):
        for tok, rx in TOKENS.items():
            if rx.search(line):
                hits.append((i, tok, line.strip()))
    return hits

# ---------------------------------------------------- the SELF-TEST.
# The fixture names, in trailing `EXPECT:` line-comment markers, exactly
# the lines the gate must report; every other line must stay silent.
_MARKER = re.compile(r'--\s*EXPECT:((?:\s+[A-Za-z_]+)+)\s*$')

def selftest():
    if not os.path.exists(LEXER_FIXTURE):
        print(f'TRUST-SURFACE SELF-TEST FAIL - {LEXER_FIXTURE} is missing')
        return 1
    with open(LEXER_FIXTURE, encoding='utf-8') as fh:
        raw = fh.read()
    want = set()
    for i, line in enumerate(raw.split('\n'), 1):
        m = _MARKER.search(line)
        if m:
            for tok in m.group(1).split():
                want.add((i, tok))
    try:
        got = {(i, tok) for i, tok, _ in scan_file(LEXER_FIXTURE)}
    except LexError as e:
        print(f'TRUST-SURFACE SELF-TEST FAIL - the lexer choked: {e}')
        return 1
    missed = sorted(want - got)
    spurious = sorted(got - want)
    if missed or spurious:
        print('TRUST-SURFACE SELF-TEST FAIL - the lexer does not agree with '
              f'{LEXER_FIXTURE}:')
        for i, tok in missed:
            print(f'    HIDDEN    {LEXER_FIXTURE}:{i} [{tok}] '
                  f'is real code and was not reported')
        for i, tok in spurious:
            print(f'    PHANTOM   {LEXER_FIXTURE}:{i} [{tok}] '
                  f'is comment/string content and was reported')
        return 1
    print(f'self-test: {len(want)} expected occurrences over '
          f'{len(raw.splitlines())} fixture lines, none hidden, none '
          f'phantom ({LEXER_FIXTURE})')
    return 0

if '--selftest' in sys.argv[1:]:
    sys.exit(selftest())
if selftest() != 0:
    sys.exit(1)

occurrences = []          # (file, line, token, text)
try:
    for rel in sources():
        for i, tok, text in scan_file(rel):
            occurrences.append((rel, i, tok, text))
except LexError as e:
    print(f'TRUST-SURFACE FAIL - the source lexer could not finish: {e}')
    print('    An unterminated string or comment means the blanking has')
    print('    desynchronised, so the scan below it would be meaningless.')
    sys.exit(1)

if '--list' in sys.argv[1:]:
    for rel, i, tok, text in occurrences:
        ok = 'ok ' if tok in ALLOW.get(rel, ()) else 'NEW'
        print(f'{ok} {rel}:{i} [{tok}] {text}')
    sys.exit(0)

bad = [o for o in occurrences if o[2] not in ALLOW.get(o[0], ())]

if bad:
    print(f'TRUST-SURFACE FAIL - compiler escapes outside the allowlist '
          f'({len(bad)}):')
    for rel, i, tok, text in bad:
        print(f'    {rel}:{i} [{tok}] {text}')
    print('    Each of these is a TCB entry invisible to `#print axioms`.')
    print('    Remove it, or add it to the allowlist in this script WITH')
    print('    the justification -- the header is the trusted-surface')
    print('    census a reviewer reads.')
    sys.exit(1)

used = {(rel, tok) for rel, _, tok, _ in occurrences}
stale = sorted((f, t) for f, ts in ALLOW.items() for t in ts
               if (f, t) not in used)
for f, t in stale:
    print(f'note: allowlist entry {f} [{t}] has no occurrence left '
          f'(it may be dropped)')

files = len({o[0] for o in occurrences})
print(f'trust surface: {len(occurrences)} escapes in {files} allowlisted '
      f'files ({len(sources())} scanned); 0 outside the allowlist')
PYEOF
