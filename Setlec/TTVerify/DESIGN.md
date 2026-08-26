# The TTVerify bridge (task #119)

> "No new stream-ordering invariant.  Nothing here changes to how the
> set-model verification works.  Same install steps, very similar
> invariant on the environment, just different interpretation and a
> typing rather than a `∈` statement." — the project owner, setting
> this task

This document records the design of `Setlec/TTVerify/*`.  It lives here
while the work is on its own branch (the same reason
`Setlec/TT/DESIGN.md` does), and folds into the top-level `DESIGN.md`
when the branch merges.

## 1. What the bridge is

A second verification path for the checker: instead of interpreting a
real `Env` + `Expr` into the set model, interpret it into the
declarative type theory of `Setlec/TT/*` and conclude with a `HasType`
derivation.  Both paths coexist; nothing in `Setlec/Model/*` is
replaced, weakened or deleted.

Layering: `Setlec/TTVerify/*` may import `Setlec/TT/*`,
`Setlec/Kernel/*` and `Setlec/Verify/*`.  The checker never imports it,
and `Setlec/TT/*` stays checker-free — every adaptation lives on this
side.  Its own `lean_lib` target is `SetlecTTV`.

The subject is the **pure knot** (`Setlec.Kernel.TypeChecker` at
`CheckM`): plain `Expr`, no arena, no caches, fuel-bounded open
recursion.  The descent from the executing checker (interned twins,
memoized knot) already exists in `Setlec/Verify/*` and is inherited;
this bridge proves nothing new about the arena or the caches.
`CoreNC.lean` is outside all of it and stays so.

## 2. The decision that shapes everything: mirror `EnvModel`

`Setlec/TT/DESIGN.md` §2.1 describes the denotation as *unfolding*
constants — definitions to their values, modeled inductives to their
`_model` artifacts — by well-founded recursion on the environment.
**Task #119 does not do that.**  It carries a valuation instead:

```
TConstVal := Name → (Name → Nat) → VExpr        -- cf. ConstVal V
denote : TConstVal → Env → (Name → Nat) → Nat → Expr → Option VExpr
```

which is `Setlec/Model/Interp.lean`'s `interpExpr` with the
set-theoretic universe replaced by the syntax, clause for clause.  The
`.const` clause reads `cval`, exactly as `interpExpr` does, and the
environment invariant records (`EnvTT.defn_eq`, transposing
`EnvModel.defn_eq`) that a definition's valuation is its body's
denotation.

This is the same theory, arrived at the way the set model already
arrives at it: **the recursion on the environment becomes the
incremental construction of the valuation as declarations install.**
That construction is the existing `checkDecl_sound` induction, it needs
no new termination argument, and it is exactly the sense in which
"there is no separate ordering concept" — the incremental extension of
the invariant *is* the stream-ordering fact.

Delta is not a rule of the type theory and is not a `refl` either: it
is an equation between denotations that the invariant already carries.

### The rest of the transposition

`EnvTT env` is `EnvModel env` field for field:

| `EnvModel` | `EnvTT` |
|---|---|
| `val : ConstVal V` | `cval : TConstVal` |
| `wf`, `val_params` | *the same* |
| `mem_type`: `val c φ ∈ˢ ⟦c.type⟧` | `has_type`: `⊢ cval c φ : ⟦c.type⟧` |
| `defn_eq` | *the same*, at `VExpr` |
| `thm_ok` (equation **+ `AnnotOk`**) | just the equation |
| `annot_ok` | **no counterpart** |
| `ind_ok`'s `Empty` clause | `empty_pinned` |
| `ind_ok`'s other clauses, `rec_rules`, `proj_ok`, `caps_ok`, `nat_ops`, `div_mod`, `reduce_ops` | stage 2; recipe in `EnvTT.lean` |

Two rows carry the whole idea.  `mem_type` becomes a typing judgment —
that is the only change of substance.  And `AnnotOk` **disappears**:
the set model's truthfulness predicate exists to reconstruct, at every
binder, facts a derivation supplies for free, so `annot_ok` has no
field and `thm_ok` loses its second conjunct.

Three further collapses worth naming, all of them consequences of
denoting into syntax rather than into sets:

* **the free-variable valuation `ρ` disappears.**  `interpExpr` needs
  `ρ : Nat → V` because a set is not a variable; here the opened binder
  *is* a variable, and which one it is follows from its own `fvar`
  index and the current depth (`fvar d` at depth `d'` is
  `.bvar (d' - 1 - d)`).  So `updV` has no counterpart, and `FvarsOk`
  (which constrains `ρ`) transposes to a context correspondence
  (which constrains `Δ`).
* **`let` denotes to its zeta reduct**, mirroring `interpExpr`'s
  `letE` clause.  `VExpr.letE` and `HasType.letE` are therefore unused
  by this bridge; they become relevant at task #117, and the two forms
  are interderivable through `HasType.zeta` regardless.
* **level comparison is trivial**, as `Setlec/TT/DESIGN.md` §2.2
  predicted: `.sort u ↦ .sort (u.eval φ)`, and two levels the checker
  calls equal are equal naturals at every `φ`.

## 3. The open obligation: first-class projections

**This is a genuine gap in `Setlec/TT/*`, found by building the
bridge, and it is not a coverage decision.**

`interpExpr` reads a `.proj` node with the untyped set operations
`sfst`/`ssnd`.  The type theory has no untyped projection: its
`psigmaFst`/`psigmaSnd` are *constants applied to the pair's type
arguments* `A` and `B`, and a `.proj` node does not carry them.  The
checker recovers them at use time by whnf-ing the subject's inferred
type (the `.proj` clause of `annotateBody`, `Setlec/Kernel/Core.lean`),
which is information a function of the expression alone does not have.

`Setlec/TT/DESIGN.md` §3 says projections "denote to applications of
`psigmaFst`/`psigmaSnd`".  For a *modeled* structure that is right —
the checker rewrites the node into a projection-function application at
annotation time, so no `.proj` survives.  For the **pinned pair** the
node is first-class by design (`ProjEntry.native`, installed only by
the `PSigma'` basis block) and survives into stored terms.  So the
sentence is true of the case where the node is gone and silent about
the case where it is not.

Making the denotation *relational* is not an escape: the defeq clause
of the fuel induction needs both sides denoted by the **same** map, or
the two existentials never meet.  Reconstructing `A` and `B` by calling
the checker's own inference is not one either: it would make the
denotation fuel- and strategy-dependent, which is precisely what this
layer exists to avoid.

**The fix — a projection former in the layer.**  Add
`VExpr.proj (i : Nat) (e : VExpr)`, interpreted by `sfst`/`ssnd`
(literally `interpExpr`'s clause), with

```
Γ ⊢ p : PSigma' u v A B                    Γ ⊢ p : PSigma' u v A B
--------------------------                 -------------------------------
Γ ⊢ proj 0 p : A                           Γ ⊢ proj 1 p : B (proj 0 p)
```

and the computation rules `proj 0 (mk u v A B a b) ≐ a`,
`proj 1 (…) ≐ b`, plus structure η `p ≐ mk (proj 0 p) (proj 1 p)`.
The type arguments are *derived from the premise* instead of carried in
the term, which is exactly how the checker's own rule works, and it
gives the layer the same payoff the `app` rule already has: the premise
hands soundness the `ve ∈ˢ sigmaSet …` package that the set model's
`AnnotOk` proj clause has to carry by hand.  `psigmaFst`/`psigmaSnd`
may then become *derivable* (`fun A B p => proj 0 p`), shrinking
`BConst` rather than growing it.

Until that lands, `denote` is `none` on `.proj` and the bridge covers
only stored terms without a first-class projection node.  The scale of
the gap, measured: 188 `proj` records in the preprocessed init-prelude
stream and at least one in 34 of the committed e2e fixtures (most of
them rewritten away at annotation, the pinned-pair ones not).

## 4. What is proved, and what the remaining hypothesis is

Stage 1 (this branch) proves, `sorry`-free and on
`[propext, Classical.choice, Quot.sound]`:

* `EnvTT.empty` — the base of the induction;
* `EnvTT.hasType_defn` / `EnvTT.hasType_thm` — the per-declaration
  conclusion ("this value has a derivation of its stated type") as a
  two-line consequence of `has_type` and `defn_eq`.  That it *is* two
  lines is the payoff of transposing `mem_type` rather than inventing a
  separate declaration-level statement;
* `foldlM_TT` / `checkDecls_TT` — the fold over the stream, reducing
  acceptance to the per-declaration step;
* `no_constant_of_Empty_TT` and `no_proof_of_Empty_TT` — the
  consistency corollary, through `Setlec.TT.no_proof_of_empty`.

The open hypothesis is exactly one: `CheckDeclTT`, "checking one
declaration preserves the derivation model" — the transpose of
`checkDecl_sound`, and the clause-by-clause fuel induction of stage 2.
It is a named `Prop` rather than a `sorry` so that every consumer of it
is visible in the source.

Note where the set theory enters: **nowhere in `EnvTT`**.  The
invariant is purely derivation-level; a `SetTheory V` instance is
needed only at `no_constant_of_Empty_TT`, where the layer's own
consistency theorem turns the pinned valuation of `Empty` into
uninhabitation.

### The direct-install hypothesis

Stage 2's step is stated for `directStructsEnabled = false`
(`Setlec/Kernel/Direct.lean`, and the top-level `DESIGN.md` section
"The master switch, and why it defaults on").  A directly installed
structure has no `_model` artifact and the denotation of a stored
inductive goes through exactly those artifacts.  **The switch defaults
on**, because turning it off costs five verdicts, so this is a real
restriction on the configuration the bridge covers and it is stated
rather than hidden.  The set model covers both settings and continues
to.

## 5. Interfaces this bridge consumes

* **Nat literals** (`Setlec/TT/Nat/*`, task #119's other half).  The
  lemma families are hypothetical over an arbitrary `f : VExpr` and
  take their recurrences at numerals only, so the layer needs no
  constant for `Nat.add` and the bridge's obligation at a certified
  fast path is: denote the checker's own certificate for that
  operation (which `EnvTT` carries, by the same mechanism that carries
  the `_model` iota theorems), instantiate it at numerals, and hand the
  resulting `Deq` equations to `numeral_add` and friends.  `String`
  literals need nothing: `strLitToConstructor` is finite and explicit.
* **Modeled iota, eta, unit-like, K.**  Not a risk: the `_model`
  theorems are stream declarations the checker *accepted*, so
  `EnvTT.has_type` already supplies a derivation of each by the time
  any later declaration fires the rule.  Firing is instantiation plus
  `trans`.  A propositional equality suffices because conversion in
  this layer is equality reflection.  K needs nothing at all — its
  guard makes it proof irrelevance (the #74 finding).
