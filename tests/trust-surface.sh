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
# NOT SCANNED: `tests/e2e/src/*.lean`.  Those are fixture *inputs* — the
# Lean sources that get exported into the streams the checker must
# REJECT — so they deliberately contain the very constructs this gate
# hunts (`tests/e2e/src/sorry_use.lean` is a `sorry`, by design).  They
# are never part of con-leche's own build.
#
# THE ALLOWLIST, and the justification for every entry (file → the
# tokens tolerated there).  A token in an allowlisted file that is not
# on its own list fails just as loudly as one in a bare file.
#
#   ConLeche/Kernel/Expr.lean          unsafe, ptrAddrUnsafe,
#                                    implemented_by, computed_field
#       The tree's ONE `implemented_by`-class escape on the verified
#       path: `@[implemented_by beqFast] Expr.beq`, a `ptrAddrUnsafe`
#       short-circuit plus an address-keyed memo, and the packed
#       `@[computed_field] data` (hash / bvar bound / fvar bound / …).
#       Both are the user's standing ruling — *"Adopt computed_fields.
#       It's a compiler feature, we trust the compiler"* (2026-09-04) —
#       and the census that argues them is `ConLeche/Cached/ExprC.lean`
#       §1–2.  Same escape class `Lean.Expr` itself lives on.
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
# WHAT IS DELIBERATELY *NOT* ALLOWLISTED, and used to be:
# `ConLeche/SetTheory/Derive/*`.  Twenty `@[implemented_by …] … unsafeCast
# ()` stubs gave the noncomputable model operators compiled garbage so
# that they could be *mentioned* in computable definitions.  Nothing
# needed that (the operators were already `noncomputable def`s, and the
# implementation may not even import them — layering.sh), so they were
# deleted on 2026-09-06 rather than allowlisted.  This gate is what
# stops them growing back.
#
# Usage: tests/trust-surface.sh [--list]   (--list prints every scanned
# occurrence, allowlisted or not — the census, for updating this header.)
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
    'ConLeche/Challenge.lean':       {'sorry'},
    'ConLeche/Kernel/Expr.lean':
        {'unsafe', 'ptrAddrUnsafe', 'implemented_by', 'computed_field'},
    'ConLeche/Kernel/Name.lean':     {'computed_field'},
    'ConLeche/Kernel/BasisGen.lean': {'unsafe', 'implemented_by'},
}

# fixture *inputs*: deliberately contain what the checker must reject
SKIP_DIRS = ('tests/e2e/src/',)

ROOTS = ('Main.lean', 'ConLeche.lean', 'PinDump.lean')

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

def code_only(src):
    """Drop block comments, line comments and string literals, keeping
    line structure so reported line numbers stay true."""
    def blank(m):
        return re.sub(r'[^\n]', ' ', m.group(0))
    src = re.sub(r'/-.*?-/', blank, src, flags=re.S)
    src = re.sub(r'"(?:\\.|[^"\\])*"', blank, src)
    src = re.sub(r'--[^\n]*', blank, src)
    return src

occurrences = []          # (file, line, token, text)
for rel in sources():
    with open(rel, encoding='utf-8') as fh:
        lines = code_only(fh.read()).split('\n')
    for i, line in enumerate(lines, 1):
        for tok, rx in TOKENS.items():
            if rx.search(line):
                occurrences.append((rel, i, tok, line.strip()))

if '--list' in sys.argv[1:]:
    for rel, i, tok, text in occurrences:
        ok = 'ok ' if tok in ALLOW.get(rel, ()) else 'NEW'
        print(f'{ok} {rel}:{i} [{tok}] {text}')
    sys.exit(0)

bad = [o for o in occurrences if o[2] not in ALLOW.get(o[0], ())]

if bad:
    print(f'TRUST-SURFACE FAIL — compiler escapes outside the allowlist '
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
