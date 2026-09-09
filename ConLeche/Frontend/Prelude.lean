module

public import ConLeche.Frontend.ExportC

@[expose] public section

/-!
# The built-in prelude (task #191)

**What it is.**  The checker's own little prelude: the six pinned
basis blocks (`Eq`, `Nat`, `PUnit`, `Empty`, `False`, `Quot` with its
soundness axiom), the `Bool` block — every declaration the
pin-certified `Nat` operations' install needs that is neither in the
operation's own dependency closure nor a stream-certified operation
itself — and the `And` block, pinned by design: the one propositional
structure whose recursor the stuck-major rescue serves
(`majorToCtor`'s `And` branch, `ConLeche/Kernel/Core.lean`, keyed on
the name), so the name must denote the toolchain's `And` in every
fold.  `ConLeche/PinGen/Prelude.lean` computes the set mechanically
(`pinnedPreludeMembers` adds `And`); the committed file is
`pins/<toolchain>.prelude.ndjson`, regenerated with
`lake exe natop-pins-export` and gated by `tests/pindump.sh`.

**Why.**  A user report (2026-09-06): the Nat-op pins were sensitive
to the stream's installation order — an export that emits
`Nat.shiftLeft` before the `Bool`/`Eq` blocks its certificate
statements are spelled over declined at the install.  The user's
directive: *"add Bool and what else is needed … and actually add them
to the env initially and unconditionally (our own little prelude).
when they come later in the stream, just compare and decline if
different."*

**How.**  The prelude is a lean4export-format stream, embedded here
with `include_str` and parsed by the ordinary direct parser
(`parseExportD`) into `DeclC` records — the basis blocks through the
same pin match as any stream's, `Bool` as an ordinary inductive block
the direct sum install serves.  Every stream parse
(`parseExportStreamD` / `parseExportHandleD`, `Main.lean`) is handed
`builtinPrelude`, which it PREPENDS to its result and DEDUPES against
(`pushDecl` in `ConLeche/Frontend/ExportC.lean`): a later stream copy of a
prelude declaration is dropped when it is the same declaration and
declines the stream when it differs.  So "in the env initially and
unconditionally" is "first in every fold": the verified fold
`checkDecls` sees `prelude ++ stream'` as one list of
records and installs the prelude by exactly the routes it installs a
stream's records by — **nothing in the kernel, the cached driver or
the proofs changed** (the main theorem quantifies over the parsed
list; the frontend sits below it, like the projection rewrite of
`ConLeche/Frontend/ProjRec.lean`).

`builtinPrelude` is a 0-ary definition, so the embedded text is parsed
once, at process initialisation (a few hundred lines).  A parse
failure — a corrupted committed file — is `.error`, which `Main.lean`
reports as exit 3 before reading any input; `tests/ConLecheTests` pins
that it parses, what it holds, and that the fold accepts it.
-/

namespace ConLeche.Frontend

/-- The committed prelude for the pinned toolchain
(`lean-toolchain`), embedded at build time.  A toolchain bump
regenerates it and re-points this path (the pin dump's `preludeFile`
names the same basename; `tests/pindump.sh` checks both). -/
def builtinPreludeText : String :=
  include_str "../../pins/leanprover-lean4-v4.33.0.prelude.ndjson"

/-- The parsed, indexed prelude: `Except` because a committed file can
in principle be corrupted, and a prelude that does not parse must be a
loud error rather than a silently empty prelude. -/
def builtinPreludeE : Except FrontendError PreludeIx :=
  (PreludeIx.ofDecls ·.decls) <$> parseExportD builtinPreludeText

end ConLeche.Frontend
