module

public import ConLeche.Frontend.ExportC
public import ConLeche.Frontend.Prepare

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
(`parseExportD`) into `Declaration` records.  `preparePrelude`
(`ConLeche/Frontend/Prepare.lean`) puts the prelude's declarations at
the front of every stream it prepares — **the stream's OWN record where
the stream has one**, and one of these only where it has none — so "in
the env initially and unconditionally" is "first in every fold", and a
stream that declares the toolchain's `Bool` is checked on its own
`Bool` record.  The records install by exactly the routes a stream's
records install by, the pinned blocks among them recognised by the fold
(`basisPinHit`, `ConLeche/Kernel/Basis.lean`).  The main theorem
quantifies over the prepared list; the frontend sits below it, like the
projection rewrite of `ConLeche/Frontend/ProjRec.lean`.

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
def builtinPreludeE : Except (CheckError × Nat) PreludeIx :=
  (fun r => ⟨r.decls⟩) <$> parseExportD builtinPreludeText

end ConLeche.Frontend
