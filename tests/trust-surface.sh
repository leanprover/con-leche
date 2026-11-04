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
#       small readable statements a reader audits — the main theorem
#       `ConLeche.model_exists` and the statement about the chunks
#       `ConLeche.no_False_declaration`, from which the main corollary
#       `ConLeche.main_no_False` is derived — with `sorry` where the
#       proofs go.  The `sorry` is the whole point of the file —
#       Comparator's contract is that
#       the challenge states the theorem and the *solution*
#       (`ConLeche/MainTheorem.lean`) proves it — and it is harmless
#       because the module is a TCB dead end: nothing in the tree
#       imports it, it roots its own `lean_lib` (`ConLecheChallenge`), and
#       that library is not in `defaultTargets`, so `lake build` never
#       builds it and no shipped or proved declaration can reach the
#       `sorryAx` it introduces.  A `sorry` anywhere else still fails
#       this gate.
#
#   ConLeche/Frontend/ReadRange.lean   extern
#       `readRangeIO` (task #450) — THE ONE NATIVE FUNCTION the checker
#       carries: the positional read `pread(2)` of a regular file, in C
#       (`native/read_range.c`, a few dozen lines), because Lean's file
#       handles have no positional read (maintainer's ruling: an
#       `[extern]` for seek/pread is allowed, a memory map is not).  It
#       is the binary's instance of the IO class's `readRange`
#       (`ConLeche/Frontend/CheckerIO.lean`), whose model is the slice
#       of the snapshot's bytes; that the C function returns that slice
#       is part of the trust assumption the IO class states (the
#       runtime's own file calls are in it already), and
#       `tests/ConLecheTests/CheckerIOTests.lean` compares the two on
#       the committed fixtures, at offsets inside, across and past the
#       end of each file.
#
#   THE BUILD AND NATIVE SURFACE (task #450) — not Lean, so not scanned
#   for tokens, but trusted all the same: the package's build file
#   (`lakefile.lean`, Lean code that Lake runs to build the binary,
#   compiling and linking the C below) and every native source in the
#   tree (`*.c`, `*.h`, `*.cc`, `*.cpp`, `*.S`, `*.s`; today
#   `native/read_range.c`, the positional read `readRangeIO`).  Each is
#   PINNED by its SHA-256 in `NATIVE` below with its reason: a change to
#   one, and a native source or a `lakefile.*` that is not listed, fails
#   the gate until a reviewer re-pins it here (the failure prints the new
#   digest).  The other projects' `lakefile.toml`s (`bridge/`,
#   `pinners/`) build no part of the binary and are not listed.
#
#   ConLeche/Kernel/Exclusive.lean     unsafe, implemented_by
#       `withExclusive` (tasks #314, #317) — THE ONE
#       `unsafe`-implemented primitive of the substitution walks.  It
#       is *defined* as `k false` and `@[implemented_by]` the compiled
#       `k (isExclusiveUnsafe a)` — the reference-count read the
#       official kernel's `replace_fn` keys its cache on
#       (`is_likely_unshared`); the walks memoise exactly the nodes it
#       reports shared.  The obligation `h : k true = k false` is what
#       justifies the substitution: the continuation cannot observe the
#       answer, so the compiled program computes the definition's
#       value — the same arrangement as `Init.Util`'s `withPtrAddr`
#       (`k 0` in the model, the address in the binary).  Every use in
#       the tree goes through `withExcl`, whose continuation returns a
#       `Squash` (a `Subsingleton`), so `h` is `Subsingleton.elim` and
#       the walks' theorems (`Verify/Cached/OpsC.lean`) hold whatever
#       the read answers.  The file's own docstring is the
#       justification (and cites the Lean RFC that proposes the
#       primitive for `Init/Util.lean`); the task #314 and #316
#       records read the generated C for the trap the primitive exists
#       to avoid (a hidden reference before the read).
#
#   ConLeche/Kernel/BasisGen.lean      unsafe, implemented_by
#       ELABORATOR-ONLY.  `#stored_basis` computes the stored basis
#       pins (the recursors' install-computed rule fields) at
#       elaboration time through `unsafe evalTerm` and splices the
#       resulting literals.  Nothing
#       here is in the binary; the spliced literals are ordinary data
#       the proofs consume.
#
#   ConLeche/Driver/Run.lean           unsafe
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
#   ConLeche/Driver/ParInstall.lean    unsafe
#       THE PARALLEL INSTALL'S OWN MARKS (task #329).  Six term-level
#       `unsafe Runtime.markPersistent` calls, the same escape as
#       above.  Two mark what lives to the end of the run: the records
#       (`ds`), once, before the first prelude task is spawned, and —
#       inside `installAndPublish`, by the installer before it
#       publishes anything — an install's result and the array of
#       constants it publishes into its slot (the constants end up in
#       the installed environment).  The other four mark the install's
#       own bookkeeping, which dies with the install and is leaked on
#       purpose (measured, task #329's `ifix` record): the base shards
#       (every lookup takes a reference on a shard entry, atomic and
#       contended if the shard were multi-threaded), the dependency
#       counts, the per-record states and the dependency edges (one
#       call, in `depsChunk`), and the assembled dependents (freeing
#       these cost the check phase more than it saved).
#       What is read-only from the mark on: the records, the shards,
#       the edges, the dependents and every published result.  The
#       counts and states are `IO.Ref`s that every worker WRITES; a
#       persistent ref is read and written through the runtime's atomic
#       path exactly like a multi-threaded one, and what is stored in
#       it is a scalar or (`RState.done`) a fresh wrapper around an
#       already persistent result, so no write races a count.
#       Results used: the records', the published result's, the slot
#       array's and the dependents' marks discard theirs (the call is
#       the identity on the value and marks the graph in place).  The
#       shard's and `depsChunk`'s are returned as their task's value:
#       logically an arbitrary inhabitant of the type, which is
#       harmless — a shard is pinned by the `BuiltShard` subtype (it
#       IS `buildShard` of some shard number, which is all
#       `buildBase_inj` needs), and the counts, states and edges only
#       schedule (a wrong one costs time or termination, never a
#       verdict: what the commit takes from a state is a `WRes`, which
#       carries its own evidence).  What every mark relies on: the marked graph reaches
#       no object that is already multi-threaded and still counted by
#       another thread (the mark would downgrade it to persistent under
#       that thread's feet).  Precisely, every object a mark reaches is
#       persistent already, or was built by the marking thread, or is
#       multi-threaded but counted by no other running thread while the
#       mark runs.  The third kind occurs twice: the dependents' mark
#       reaches the per-chunk arrays `dependentsChunk` marked
#       multi-threaded (their tasks have finished, and only the marking
#       thread holds them); a base shard's mark reaches the projection
#       tables' `Name`s `predictChunk` built, multi-threaded and shared
#       with the prediction's `slots` array (their tasks have finished,
#       the main thread holding `slots` is waiting for the shards, and
#       the other shard tasks take references only on the names of their
#       own shards: a name lies in one shard).  The results' mark
#       reaches only the first two kinds (the warning sits at its
#       call).  `--no-mark-persistent`
#       turns all six off at once (the
#       bookkeeping is then multi-threaded), which is how the A/B is
#       measured on the shipped binary.
#   ConLeche/Driver/OwnerParse.lean    unsafe
#       THE ROUNDS PARSE'S MARKS (task #329).  One term-level
#       `unsafe Runtime.markPersistent` call (`markOne`, through
#       `markEach` and `markSlots`), the same escape as above, taken by
#       every owner thread on what it built before it hands it out: the
#       table entries of round 0 (`markSlots`: the slots that hold an
#       entry, not the late slots' filler) and of each later round, and
#       the chunk's records; never on an array or any other container,
#       which the parse drops later.  Every marked object is read-only
#       from the mark on and, but for two small exceptions, lives to the
#       end of the run (the tables' entries are the declarations'
#       parts): a window that falls back leaks what its owners marked
#       (the serial parse rebuilds those entries), and a name entry that
#       only binders read is reached by no declaration (a parsed
#       binder's name is anonymous), so it outlives its use.  The call
#       is the identity on the value: nothing the parse returns, and no
#       step of the proof that it is the serial parse's (`GOK.window`:
#       every stored entry is GOOD, a property of the round functions),
#       can turn on whether the mark happened.  `--no-mark-persistent`
#       turns it off.
#       The marks rely on one invariant: every object reachable from a
#       newly built entry was built on this thread since its last
#       publication, or is already persistent (entries of the finished
#       tables and of earlier rounds, which the builders share), so the
#       mark never walks into an object another thread is counting.  A
#       late slot's filler breaks it — a constant every owner pushes —
#       which is why `markSlots` skips late slots.  In the compiled
#       binary that filler is a closed term, persistent already; in the
#       interpreter (the `#eval` tests, `RoundsTests`, run with marking
#       on) closed-term fillers are ordinary shared objects, and marking
#       one while other threads counted it corrupted the heap.  So the
#       interpreted tests exercise that hazard, which the shipped binary
#       does not have; they do not test the binary's own marks.
#
#       Run.lean took its escape over from `Main.lean` when the
#       proof-carrying driver split out of it into `ConLeche/Driver/*`;
#       `Main.lean` itself is the entry point (the plumbing around
#       `runArgs`, then the exit)
#       and tolerates no escape.
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
    'ConLeche/Driver/Run.lean':       {'unsafe'},
    'ConLeche/Driver/ParInstall.lean': {'unsafe'},
    'ConLeche/Driver/OwnerParse.lean': {'unsafe'},
    'ConLeche/Challenge.lean':       {'sorry'},
    'ConLeche/Kernel/Expr.lean':     {'computed_field'},
    'ConLeche/Kernel/Name.lean':     {'computed_field'},
    'ConLeche/Kernel/BasisGen.lean': {'unsafe', 'implemented_by'},
    'ConLeche/Kernel/Exclusive.lean': {'unsafe', 'implemented_by'},
    'ConLeche/Frontend/ReadRange.lean': {'extern'},
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

# ---------------------------------- THE BUILD AND NATIVE SURFACE (task #450).
# Pinned by content: path -> (sha256, reason).  See the header.
import hashlib
NATIVE = {
    'lakefile.lean': ('f5a0416b3ac7ba58cbdeb6074cf14239601386539c99c8f8ec04100c729bf171',
        'the build: the targets, and the C compile and link of native/'),
    'native/read_range.c': ('6ffff889161f74962d0633e2b906523bfc85b3d4ef68ab80da4160f3d0d7c821',
        'readRangeIO, the positional read behind CheckerIO.readRange'),
}
NATIVE_EXT = ('.c', '.h', '.cc', '.cpp', '.S', '.s')
found = set(f for f in os.listdir('.') if f.startswith('lakefile.'))
for dp, dirs, fs in os.walk('.'):
    dirs[:] = [d for d in dirs if d not in ('.lake', '.git', '_tmp')]
    for f in fs:
        if f.endswith(NATIVE_EXT):
            found.add(os.path.relpath(os.path.join(dp, f), '.'))
nat_bad = []
for rel in sorted(found | set(NATIVE)):
    if not os.path.exists(rel):
        nat_bad.append(f'{rel}: pinned but missing (drop its entry)')
        continue
    with open(rel, 'rb') as fh:
        h = hashlib.sha256(fh.read()).hexdigest()
    if rel not in NATIVE:
        nat_bad.append(f'{rel}: not pinned (sha256 {h}); add it to NATIVE with its reason')
    elif NATIVE[rel][0] != h:
        nat_bad.append(f'{rel}: changed (sha256 {h}); review it, then re-pin it in NATIVE')
if nat_bad:
    print(f'TRUST-SURFACE FAIL - the build and native surface ({len(nat_bad)}):')
    for b in nat_bad:
        print(f'    {b}')
    sys.exit(1)
print(f'build and native surface: {len(NATIVE)} files pinned '
      f'({", ".join(sorted(NATIVE))})')

# ---------------------------------------- THE CHECKER-IO FENCE (task #450).
# The modules written against the checker's IO class (`CheckerIO`,
# `ConLeche/Frontend/CheckerIO.lean`) are run at `IO` by the binary and
# reasoned about at the model `ModelIO` by the proofs.  The trust
# assumption the class states needs these modules to reach the runtime
# only through the class: its file operations (whose model is the
# snapshot) and its escape `CheckerIO.liftIO` (whose model is every
# outcome).  THIS IS A TEXTUAL CHECK, not a proof: over each module's
# code (comments and string literals blanked, interpolations kept),
# with the argument of every `CheckerIO.liftIO` cut out (the rest of
# its line, any bracket it opens up to its close, and, when the line
# ends in `do` or with the argument still to come, every following line
# indented deeper than the line itself) and the named declarations of
# the binary's instance cut out, no name of the runtime is left: `IO`
# (but `IO.Error`, the class's error type), `BaseIO`, `EIO`, `ST`,
# `EST`, `StateRefT`, `Task`, `dbgTrace`/`dbg_trace`, `initialize`, a
# mutex/channel/condition variable, a file handle, `readRangeIO`, or a
# runtime file operation by its name (`pathExists`, `realPath`,
# `readBinFile`, `metadata`, `isDir`, …, except as the class's own
# `CheckerIO.<op>`).  It does not follow imports or definitions: a
# helper defined elsewhere that does IO under a pure type
# (`unsafe`/`implemented_by`/`extern`, which the scan above confines to
# its allowlist) or a value of a structure of `IO` functions passed in
# would pass it, so what the fenced modules import is reviewed with
# them; and it does not see through a notation that expands to a
# runtime call.  A module joins the list when it is converted.
IO_FENCE = {
    # path: the declarations cut out whole (the instance and what only
    # it calls; the class's own `liftIO` field, whose type is `IO α → m α`)
    'ConLeche/Frontend/CheckerIO.lean': ('class CheckerIO', 'def readRangeOf',
                                         'instance instCheckerIOIO',
                                         # the model's instance: its fields are
                                         # named as the operations are
                                         'instance : CheckerIO ModelIO'),
    'ConLeche/Frontend/Stream.lean': (),
    'ConLeche/Driver/StreamParse.lean': (),
    'ConLeche/Driver/CheckMain.lean': (),
    'ConLeche/Driver/Dispatch.lean': (),
    'ConLeche/Driver/Cli.lean': (),
}
IO_OPS = ('pathExists', 'realPath', 'readBinFile', 'readFile', 'readRange', 'fileSize',
          'metadata', 'isDir', 'readDir', 'walkDir', 'lines', 'writeFile', 'writeBinFile',
          'removeFile', 'removeDirAll', 'createDir', 'createDirAll', 'rename',
          'appDir', 'currentDir', 'getEnv', 'setEnvVar')
IO_RX = re.compile(
    r'\b(?:IO|BaseIO|EIO|ST|EST|StateRefT|Task|dbgTrace|dbg_trace|initialize|'
    r'builtin_initialize|Mutex|Channel|Condvar|Handle|readRangeIO)\b(?!\.Error\b)'
    r'|(?<!CheckerIO)\.(?:' + '|'.join(IO_OPS) + r')\b'
    r'|(?<![\w.])(?:' + '|'.join(IO_OPS) + r')\b(?=\s)')
LIFT = 'CheckerIO.liftIO'

def indent_of(line):
    return len(line) - len(line.lstrip(' '))

def cut_lift_args(code):
    """Blank the argument of every `CheckerIO.liftIO` (see above)."""
    lines = code.split('\n')
    k = 0
    while k < len(lines):
        line = lines[k]
        at = line.find(LIFT)
        if at < 0:
            k += 1
            continue
        start = at + len(LIFT)
        rest = line[start:]
        # the rest of the line, and any bracket it leaves open
        depth = sum(rest.count(c) for c in '([{') - sum(rest.count(c) for c in ')]}')
        lines[k] = line[:at] + 'LIFTED' + ' ' * (len(line) - at - len('LIFTED')) \
            if len(line) - at >= len('LIFTED') else line[:at] + 'LIFTED'
        base = indent_of(line)
        tail = rest.strip()
        block = tail == '' or tail.endswith(' do') or tail == 'do' or tail.endswith('(')
        m = k + 1
        while m < len(lines) and (depth > 0 or (block and (lines[m].strip() == '' or
                                                            indent_of(lines[m]) > base))):
            depth += sum(lines[m].count(c) for c in '([{') - \
                sum(lines[m].count(c) for c in ')]}')
            lines[m] = ''
            m += 1
        k = m if m > k + 1 else k + 1
    return '\n'.join(lines)

def cut_decls(code, heads):
    """Blank the named top-level declarations, each up to the next line
    that starts in column 0."""
    lines = code.split('\n')
    k = 0
    while k < len(lines):
        if any(lines[k].startswith(h + ' ') or lines[k] == h for h in heads):
            lines[k] = ''
            k += 1
            while k < len(lines) and (lines[k] == '' or lines[k][0] == ' '):
                lines[k] = ''
                k += 1
        else:
            k += 1
    return '\n'.join(lines)

# the fence's self-test: what it must see, and what it must not
_fence_probe = '''def f [CheckerIO m] : m Unit := do
  CheckerIO.liftIO do
    IO.println "x"
    let _ ← IO.monoMsNow
  let _ ← CheckerIO.liftIO (IO.println
    "y")
  let _ ← CheckerIO.readBinFile p
  let _ ← CheckerIO.liftIO IO.monoMsNow
  IO.println "seen"
  let _ ← p.pathExists
def g : IO Unit := pure ()
'''
_fence_hits = [i for i, l in enumerate(cut_lift_args(cut_decls(code_only(_fence_probe),
    ())).split('\n'), 1) if IO_RX.search(l)]
if _fence_hits != [9, 10, 11]:
    print(f'CHECKER-IO FENCE SELF-TEST FAIL: hits at {_fence_hits}, expected [9, 10, 11]')
    sys.exit(1)

io_bad = []
for rel, heads in IO_FENCE.items():
    with open(rel, encoding='utf-8') as fh:
        raw = fh.read()
    code = cut_lift_args(cut_decls(code_only(raw, rel), heads))
    for i, line in enumerate(code.split('\n'), 1):
        if IO_RX.search(line):
            io_bad.append((rel, i, line.strip()))
if io_bad:
    print(f'CHECKER-IO FENCE FAIL - a module written against CheckerIO reaches '
          f'the runtime outside CheckerIO.liftIO ({len(io_bad)}):')
    for rel, i, text in io_bad:
        print(f'    {rel}:{i} {text}')
    sys.exit(1)
print(f'checker-io fence (textual): {len(IO_FENCE)} modules reach the runtime only '
      f'through CheckerIO')

# ------------------------------------------ THE ONE EXIT (task #450).
# The trust assumption of the IO class says the actions passed to
# `CheckerIO.liftIO` do not themselves end the process with an exit code:
# the exit code the theorems speak of is the one `runArgs` returns, and
# `main` exits with it.  TEXTUAL, over the code of every scanned file:
# `IO.Process.exit` (under any spelling of its name) is in `Main.lean`,
# twice: `IO.Process.exit code` and, when the abort variables cannot be
# set, before `runArgs` starts, `IO.Process.exit 3`.  The C function is
# pinned above and calls no exit.  And `Main.lean`, read and not proved,
# declares only `enableAbortOnNonlinear` and `main`.
EXIT_RX = re.compile(r'\bProcess\.exit\b|\blean_io_exit\b|\bopen\s+IO\.Process\b')
exit_hits = []
for rel in sources():
    with open(rel, encoding='utf-8') as fh:
        raw = fh.read()
    for i, line in enumerate(code_only(raw, rel).split('\n'), 1):
        if EXIT_RX.search(line):
            exit_hits.append((rel, i, line.strip()))
if [(h[0], h[2]) for h in exit_hits] != [('Main.lean', 'IO.Process.exit 3'),
                                         ('Main.lean', 'IO.Process.exit code')]:
    print(f'ONE-EXIT FAIL - IO.Process.exit must appear as `IO.Process.exit 3`, then '
          f'`IO.Process.exit code`, in Main.lean; found:')
    for rel, i, text in exit_hits:
        print(f'    {rel}:{i} {text}')
    sys.exit(1)
with open('Main.lean', encoding='utf-8') as fh:
    _main_top = [l.strip() for l in code_only(fh.read(), 'Main.lean').split('\n')
                 if l.strip() and not l[0].isspace()]
_main_expected = ['module', 'public import ConLeche.Driver.Cli',
                  'public import Std.Async.System', '@[expose] public section',
                  'def enableAbortOnNonlinear : IO Unit := do',
                  'def main (args : List String) : IO Unit := do']
if _main_top != _main_expected:
    print(f'MAIN FENCE FAIL - Main.lean must declare only `enableAbortOnNonlinear` and '
          f'`main`; its top level is:')
    for l in _main_top:
        print(f'    {l}')
    sys.exit(1)
print('one exit (textual): IO.Process.exit only in Main.lean, the code and the abort '
      'variables\' 3; Main.lean declares only enableAbortOnNonlinear and main')

files = len({o[0] for o in occurrences})
print(f'trust surface: {len(occurrences)} escapes in {files} allowlisted '
      f'files ({len(sources())} scanned); 0 outside the allowlist')
PYEOF
