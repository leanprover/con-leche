module

public import Init.Util

/-!
# InLean: `withIsExclusive`, the reference-count read behind the walk memos

Twin of con-leche's `ConLeche.Kernel.Exclusive`, and a copy of the standard
library's `withIsExclusive` (`Init.Util`, after Lean v4.35.0), with the same
name, signature and definitions, for toolchains that lack it.  The core copy
of InLean does not have this module: the generator drops it and the core
copy uses `Init.Util`'s (`scripts/inlean-sync.py`).

`withIsExclusive a k h` runs `k` on whether the object `a` is *exclusive* —
single-threaded with reference count exactly 1, so that no other reference
to it exists.  In the logic it is `k false` ("not known to be exclusive");
in compiled code `@[implemented_by]` substitutes `k (isExclusiveUnsafe a)`,
the count read off the object header (`lean_is_exclusive_obj`, a BORROWED
parameter).  A multi-threaded object and a persistent one answer `false`,
the safe side.

**What justifies the substitution** is the obligation `h : k true = k false`:
the continuation's value does not depend on the answer, so the compiled
program computes the value the definition names.  A caller may use the
answer to choose *how* to compute a value, never *which* value — the
arrangement of `Init.Util`'s `withPtrAddr`.

**What it is for.**  A walk's memo exists so that a node reached twice — a
shared sub-DAG — is visited once.  A node with exactly one reference cannot
be reached twice, so recording it is pure loss; the official kernel's
`replace_fn` caches a node only when `!is_likely_unshared(e)`, the same read.
The walks (`InLean.ExprOps`) and the equalities (`InLean.ExprEq`) return a
`Squash` (a subsingleton), so `h` is `Subsingleton.elim` (`withExcl`).

**The borrowed-parameter requirement.**  An owned parameter, a `let` keeping
the object alive across the call, a closure capturing it or a `Prod` holding
it is a second reference, and the read then answers `false` for every node.
The object is borrowed (`@&`) down to the `@[extern]` call, and the walks
pass their node borrowed, so the count read is the count of references
inside the term.

**Trust.**  The one `unsafe`-implemented primitive of InLean: the trust
surface gate allowlists this file for `unsafe` and `implemented_by`, with
this docstring as the justification.  Nothing is taken on faith beyond what
`withPtrAddr` already asks — that `lean_is_exclusive_obj` returns a `Bool`
and has no other effect; *which* `Bool` is irrelevant to every theorem, by
`h`.
-/

@[expose] public section

namespace InLean

set_option linter.unusedVariables.funArgs false in
/-- The compiled `withIsExclusive`: the continuation on the object's real
exclusivity. -/
@[inline] unsafe def withIsExclusiveUnsafe {α : Type u} {β : Type v} (a : @& α)
    (k : Bool → β) (h : k true = k false) : β :=
  k (isExclusiveUnsafe a)

/-- Run `k` on whether `a` is an exclusive object (reference count 1) in
compiled code; in the logic, on `false`.  The obligation says the
continuation's value does not depend on the answer. -/
@[implemented_by withIsExclusiveUnsafe]
def withIsExclusive {α : Type u} {β : Type v} (a : @& α) (k : Bool → β)
    (h : k true = k false) : β :=
  k false

end InLean
