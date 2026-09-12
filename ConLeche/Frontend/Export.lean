module

public import ConLeche.Kernel.Canon

@[expose] public section

/-!
# Reading lean4export ndjson files: the shared scaffolding

The lean4export NDJSON format (version 3.x, see `format_ndjson.md` in
the lean4export repository) is a sequence of JSON objects: an initial
`meta` object, then name/level/expression table entries (keys
`in`/`il`/`ie` give the table index) interleaved with declarations.
Index 0 of the name table is `Name.anonymous`, index 0 of the level
table is `Level.zero`; both are implicit.  Indices need not be dense or
in order (hand-crafted arena tests have gaps), so the tables are
partial maps (`IdTable`, a dense array with a sparse overflow);
entries are resolved eagerly when inserted, so a later re-binding of an
index cannot retroactively change anything built earlier.

**This file is the representation-free half** — the pieces the parse
proper is written against and would otherwise duplicate:

* `FrontendError` and the error monad `M`.

The level-parameter canonicalization the pinned blocks are matched up
to (`canonLevel`/`canonExpr`/`ConstantInfo.canon` and the lockstep
`canonEq*` twins) used to live here.  It moved to
`ConLeche/Kernel/Canon.lean` at task #293, with the matching itself:
recognising a pinned basis block or a quotient record is the FOLD's,
and the kernel may not import the frontend.

The stream's **grammar** is not here: since task #256 the dialect has
one recogniser, `ConLeche/Frontend/Scan/{Types,Fast}.lean` (the syntax
records and the byte scanner), and the `Lean.Json` DOM this file used
to read records out of is gone from the checking path.

**The parse proper is `ConLeche/Frontend/ExportC.lean`** (task #171): it
reads the stream *directly* to `Expr` — no arena, no conversion
detour.  Until task #172 this file also held a second parse into an
interned arena (`State`, `parseExport`, `parseExportStream`,
producing `DeclP` over a `WFStore`); that went with the interned
representation.

Declaration kinds the checker cannot represent yet map to
`FrontendError.unsupported`, which the driver turns into the arena's
"declined" exit code — as opposed to malformed input, which is a hard
error.  A record that CONTRADICTS ITSELF — an inductive block whose
redundant fields disagree with the block's own declarations (task
#271, issues #5 and #7) — maps to `FrontendError.invalid`, the
arena's "rejected" exit code: the stream is well formed and says
something false about a declaration official's replay regenerates and
compares.
-/

namespace ConLeche.Frontend

inductive FrontendError where
  | parseError (line : Nat) (msg : String)
  | unsupported (what : String)
  /-- The stream contradicts itself: exit 1 (task #271). -/
  | invalid (what : String)

/-- What a declaration record can carry out of the parse when it does
not produce a state: a positive DECLINE (a feature the checker does
not support) or a REJECT (task #271: the record's redundant fields
contradict the block's own declarations, which official's replay
regenerates and compares — "Invalid constructor", "Invalid recursor",
"duplicate constructor name", "No such constructor"). -/
inductive RecordVerdict where
  | declined (what : String)
  | invalid (what : String)

/-- The frontend error a record verdict becomes. -/
def RecordVerdict.toError : RecordVerdict → FrontendError
  | .declined what => .unsupported what
  | .invalid what => .invalid what

/-! ### The tree-size budget, retired at task #215

The frontend used to cap a declaration's *unshared tree size*
(`declTreeSizeBudget = 2^25`, its override, `sizeSentinel`,
`budgetedName`, the per-entry `sizes` counter).  It existed because
four record kinds were read by **unmemoized** tree walks, and a
heavily DAG-shared declaration would have unfolded them into billions
of nodes — Mathlib's `ModularCurve.JZeroGoodReductionSpecialization_alt`
is a 5 038-entry DAG whose recursor rule is 38 795 167 nodes unshared,
and it is the record that hit the cap in practice.

Task #215 removed the reasons instead of the declarations:

* the **basis-pin match** selects its candidate by *name* first
  (`ExportC.lean`), so `canonExpr` runs only on a block whose members
  are named exactly as one of the five pins';
* `Expr.renameConsts` and the `Expr.instantiate1` inside
  `openPisAtFvars` are **memoized DAG walks**, swapped in by
  `@[csimp]` in `ConLeche/Kernel/ExprOps.lean` — kernel-checked
  against the pure definitions, so no proof and no trust point moved.

What replaces the cap is a **gate, not a limit**: the adversarial
DAG-tower fixtures in `tests/e2e` put a shared tower of depth 60
(about `2^60` nodes unshared, 60 entries as a DAG) into every record
kind the frontend reads.  An unmemoized walk over one of them never
finishes, so the fixture fails and names the walker — which is what a
regression should do, rather than telling a user with a legitimate
declaration "no".  User ruling, 2026-09-07: *"delete it if it is
unlikely to help (and we know such DAGs appear in practice)."* -/

abbrev M := Except String

end ConLeche.Frontend
