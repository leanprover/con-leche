module

@[expose] public section

/-!
# The exclusivity oracle (task #314)

**One compiler escape, and why it is admissible.**  The per-walk memo
tables of the substitution walks (`ConLeche/Cached/ExprOpsC.lean`)
exist for one reason: a node reached twice — a shared sub-DAG — must be
rebuilt once, so that the walk is `O(DAG)` and its OUTPUT stays shared.
A node with exactly one reference cannot be reached twice, so recording
it is pure loss: the key, the bucket cell, the rehash.  The official
kernel's `replace_fn` (`src/kernel/replace_fn.cpp`) therefore caches a
node's replacement only when `!is_likely_unshared(e)` — the reference
count read off the object header.  This module is that read, in the
shape the tree already uses for the address reads behind `Expr.beq`:

* `isExclusiveUnsafe` (`Init/Util.lean`, `@[extern
  "lean_is_exclusive_obj"]`, a BORROWED parameter) answers `true` iff
  the object is single-threaded with reference count exactly 1
  (`lean_is_exclusive`, `lean.h`).  A multi-threaded object (count
  `< 0`) and a persistent one (count `0` — the installed environment
  after the driver's `Runtime.markPersistent`) answer `false`: "not
  known to be exclusive", the safe side.
* `withExclusive a k h` is *defined* as `k false` — the pure model
  presumes nothing exclusive, i.e. it is the always-memoised walk —
  and `@[implemented_by withExclusiveUnsafe]` substitutes the real
  answer in compiled code.  The obligation `h : ∀ b₁ b₂, k b₁ = k b₂`
  is what licenses the substitution: the continuation cannot observe
  the answer, so the compiled program computes the same value as the
  definition it replaces.  `Init.Util`'s `withPtrAddr` is the same
  arrangement (`k 0` in the model, the address in the binary, the
  continuation address-blind by obligation).

Nothing here is taken on faith beyond what `withPtrAddr` already asks:
the runtime's promise that `lean_is_exclusive_obj` returns a `Bool`
and has no other effect.  Which `Bool` it returns is irrelevant to
every theorem, by `h`.  How the walks discharge `h`: their result is a
`Squash` — a `Subsingleton`, exactly as `Expr.beqGo`'s `BeqOut` is —
carrying the rebuilt term with its proof of correctness beside an
unobservable memo, so `h` is `Subsingleton.elim` (`withExcl`).

**The obligation cannot be weakened to the visible component.**  A
continuation returning the term beside a *bare* memo has
`k true ≠ k false` (the memo differs), and an obligation on the term
alone would leave the compiled memo — which later nodes probe — outside
the theorem.  The quotient is what makes the proof honest: the memo's
content is invisible to the type, its correctness is carried in the
memo's own type (`ConLeche/Cached/ExprOpsC.lean`, the `*XInv`
invariants), and the result's term is fixed by its subtype.

**The trap this module exists to avoid** (the maintainer's ask, task
#314: *"carefully read the IR to see if that function is not itself
increasing the RC!"*): an owned parameter, a `let` keeping the object
alive across the call, a closure capturing it, or a `Prod` holding it
is a second reference, and the check then answers `false` for every
node.  The primitive is `@[inline]` all the way to the `@[extern]`
call with the borrowed parameter, and the walks pass their node
BORROWED (`@&`) so that the count the check reads is the count of
references *inside the term*; the generated C is read in the task
#314 record (DESIGN.md).

Allowlisted in `tests/trust-surface.sh` (`unsafe`, `implemented_by`).

**Written to be lifted into `Init/Util.lean` verbatim** if it proves
useful: the two definitions below have no dependency on this tree.
-/

namespace ConLeche

set_option linter.unusedVariables.funArgs false in
/-- The compiled `withExclusive`: the continuation on the object's real
exclusivity.  Inlined into its caller, so the object reaches the
`@[extern]` check as the caller's own variable — BORROWED by the
check's signature — and the call adds no reference; the continuation
receives only the `Bool`.  (`implemented_by` demands the exact type of
`withExclusive`, so `a` carries no `@&` here; the borrow that matters
is `isExclusiveUnsafe`'s.) -/
@[inline] unsafe def withExclusiveUnsafe {α : Type u} {β : Type v} (a : α)
    (k : Bool → β) (h : ∀ b₁ b₂, k b₁ = k b₂) : β :=
  k (isExclusiveUnsafe a)

/-- Run `k` on whether `a` is an exclusive object — single-threaded
with reference count 1, so that no other reference to it exists — in
compiled code; in the logic, on `false`.

The obligation `h` says the continuation's value does not depend on
the answer, so the substitution is invisible: a caller may use the
answer only to choose *how* to compute a value, never *which* value —
typically to skip a memo probe for an object that cannot be reached
again.  The pattern of `withPtrAddr`. -/
@[implemented_by withExclusiveUnsafe]
def withExclusive {α : Type u} {β : Type v} (a : α) (k : Bool → β)
    (h : ∀ b₁ b₂, k b₁ = k b₂) : β :=
  k false

/-- `withExclusive` into a subsingleton: the obligation is
`Subsingleton.elim` (the `Expr.withAddr` shape). -/
@[inline] def withExcl {α : Type u} {β : Type v} [Subsingleton β] (a : α)
    (k : Bool → β) : β :=
  withExclusive a k (fun _ _ => Subsingleton.elim _ _)

end ConLeche
