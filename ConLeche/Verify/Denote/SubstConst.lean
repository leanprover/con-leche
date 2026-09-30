module

public import ConLeche.Verify.Denote.Install
import ConLeche.Verify.Denote.VClosed
import ConLeche.Verify.Denote.Shift

public section

/-!
# Substituting the operation for its own constant

`certifyNatEqs` certifies the structural-`Nat` recurrences in the
**pre-insertion** environment with the operation's self-references
replaced by its stored value (`Expr.substConst0`); the div/mod
certificates make the same move with `substConstAll`.  Verifying an
install therefore has to move facts across that substitution — from
"`⟦substConst0 c v e⟧` in `env`" to "`⟦e⟧` in `c₀ :: env` under
`acvalWith acval c A`" (`denoteMeta_substConst0`, `Model/NatEqs.lean`).
The two sides denote to the *same* term, because `acvalWith` sends `c`
to `v`'s denotation, which is what `substConst0` writes in its place.
This module holds the lemma's fragment predicate.

**`substConst0` is shallow** — it recurses through `.app` and stops —
so the lemma is restricted to the fragment the equations live in
(`sort`, `const`, `fvar`, `app`); `natOpEquations`' sides are spines
over constants and two free variables, with no binder anywhere.
-/

namespace ConLeche.Verify

open ConLeche.Term

/-- The fragment `Expr.substConst0` is faithful on: application spines
over constants, sorts and free variables. -/
@[expose] def shallowE : Expr → Bool
  | .sort _ => true
  | .const _ _ => true
  | .fvar _ _ => true
  | .app f a => shallowE f && shallowE a
  | _ => false

end ConLeche.Verify
