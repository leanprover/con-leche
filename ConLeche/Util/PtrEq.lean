module

public import Init.Util

public section

/-!
# Vendored `withPtrEq` (the pre-2026-09-21 safe shape)

con-agua's toolchain (`leanprover/lean4:nightly-2026-10-20`) carries a change,
dated 2026-09-21 upstream, that deprecates the old `Init.Util.withPtrEq` and
replaces it with an `unsafe def withPtrEq ... := withPtrEqUnsafe a b k h` — no
longer definitionally `k ()`, so it can't be used in a kernel-checked
declaration, and `ConLeche`'s proofs that relied on that definitional equality
(`Name.beqPtr_eq`, `OwnerParse`'s `sameB_eq`, `ParInstall`'s slot check) stop
elaborating. See `vendor/README.md` for the three call sites and what broke.

This file restores the *old* shape under our own name, verbatim as it reads in
`leanprover/lean4:v4.35.0`'s `src/lean/Init/Util.lean:126-130` (before the
deprecation): a genuinely safe `def withPtrEq ... := k ()`, `@[implemented_by]`
the still-public, still-unsafe `withPtrEqUnsafe` for the compiled/runtime
version. `withPtrEqUnsafe` itself is unchanged upstream (still `public`, still
takes the same `{α : Type u} (a b : α) (k) (h)` shape; nightly-2026-10-20's
`Init/Util.lean:156-158` gates it the same way).

Unlike `Init.Util`'s own (now-deprecated) version, ours is `@[expose]`: the
three call sites need its body (`k ()`) visible to unfold through an ordinary
`public import`, with no `import all` trick, because each call site is itself
a `public` declaration and a public declaration may not depend on a privately
imported name (Lean's module system rejects that with "Unknown identifier …
is imported privately").

Soundness is exactly as before: `withPtrEq` is unsound *in general* (the classic
`Prop`/erased-data counterexample is in `withPtrEqUnsafe`'s own docstring), so
every call site must independently justify that pointer-equality implies
logical equality for its own type — which is exactly what con-leche's three
call sites already do (`Name`, `OwnerParse`'s key type, `ParInstall`'s `CacheInfo`
are all ordinary non-`Prop` inductives). We are not changing that trust
boundary, only restoring the old upstream shape under our own name.
-/

/-- See the module docstring: the old (pre-2026-09-21) safe `withPtrEq`,
`@[implemented_by]` `Init.Util.withPtrEqUnsafe` for the compiled version.

Declared as `ConLeche.withPtrEq` (not bare `withPtrEq`) because the root name
is already taken by `Init.Util`'s now-`unsafe` one; call sites use the
qualified name `ConLeche.withPtrEq` to avoid any ambiguity with that root
declaration. -/
@[expose, implemented_by withPtrEqUnsafe]
def ConLeche.withPtrEq {α : Type u} (a b : α) (k : Unit → Bool) (h : a = b → k () = true) : Bool := k ()
