# The declarative type-theory layer (task #74)

> "We are coupling verification of the concrete code too much to the
> semantic argument of consistency.  Much about the checker
> implementation (e.g. defeq unfolding) is irrelevant for the
> consistency argument.  The goal is to introduce a layer of
> separation."  — the project owner, setting this task

This document records the design of `Setlec/TT/*`.  It should be folded
into the top-level `DESIGN.md` when the branch merges; it lives here
while the work is on its own branch so that four parallel lines of work
do not collide at the end of one file.

## 1. What the layer is

A *declarative*, non-algorithmic presentation of the extensional type
theory setlec actually implements.  It is a separate module hierarchy
with its own term language (`VExpr`), its own typing judgment
(`HasType`), and its own soundness/consistency proof against the same
`SetTheory` interface the checker's model uses.

The end state this serves: the checker's verification retargets onto
this layer as its model, via a *bridge* — a denotation function from a
real `Env` + `Expr` into `VExpr` plus the theorem "checker accepts ⇒ a
`HasType` derivation exists".  After that, changing the checker's
reduction strategy perturbs the bridge, not the consistency argument.

### Layering (binding, and enforced by the imports)

| module | may import |
|---|---|
| `Setlec/TT/Syntax.lean` | nothing |
| `Setlec/TT/Subst.lean` | `TT/Syntax` |
| `Setlec/TT/Const.lean` | `TT/Subst` |
| `Setlec/TT/Judgment.lean` | `TT/Const` |
| `Setlec/TT/Examples.lean` | `TT/Judgment` |
| `Setlec/TT/Semantics/*` | the above **plus `Setlec/SetTheory/*` only** |

Nothing in `Setlec/Kernel/*`, `Setlec/Model/*` or `Setlec/Verify/*` is
imported anywhere in the hierarchy — not even by the semantics, which
restates the basis values (`Setlec/TT/Semantics/Value.lean`) directly
over the `SetTheory` interface rather than reusing
`Setlec/Model/BasisVal.lean`.  Conversely nothing in the existing tree
imports `Setlec/TT/*` yet; the layer needs its own `lean_lib`
(`SetlecTT`, rooted at `Setlec/TT.lean`) to be built at all.

## 2. The four design decisions that shape everything

### 2.1 No global environment, and no context of opaque constants

There is **no `Env`, no delta rule, and no context of assumptions**.
The justification is a real theorem about our corpus, not a
convenience: *every constant setlec accepts either (a) has a value, or
(b) has a checked model artifact that plays the role of a value, or (c)
is one of the finitely many pinned standard axioms.*  Concretely

* ordinary definitions and theorems unfold to their value;
* `opaque` declarations have a value — the checker's refusal to unfold
  one is a *restriction* (it accepts strictly less), so permitting the
  unfolding here preserves the direction the bridge needs;
* the compiler-trust family installs as `opaque` realized by
  `True.intro`, so it unfolds;
* modeled inductive types, their constructors and recursors are opaque
  *in the checker*, but the preprocessor emits `T._model` built from the
  basis formers and the install **checks** the opaque constant against
  it, so in the layer they unfold to the model — and the installed
  iota/eta rules become **derivable** from basis β/ι rather than
  assumed;
* directly-installed simple structures (task #82) unfold to their tower
  encoding;
* only the pinned standard axioms have no value at all, and there are
  finitely many, so they are **built-in rules/constants**;
* `Quot` is genuinely primitive and joins the basis.

Two consequences worth stating plainly.

**Consistency is absolute.**  With no context there is no "satisfiable
context" side condition: `Setlec/TT/Semantics/Consistency.lean` proves
outright that no closed term has type `Empty`.

**The layer is an UPPER BOUND on the checker, not a characterization.**
Setlec deliberately never aliases `T := T._model` (standing ruling:
modeled inductives are stored opaque) precisely so that streams cannot
see through the encoding.  A theory that *does* unfold `T` therefore
proves equations the checker rejects.  That is harmless for our purpose
— the bridge direction is "checker accepts ⇒ TT derivable", so a
stronger theory is a *weaker* obligation, and it is the consistency of
the TT that carries the argument — but no completeness claim can be
read off this layer.  It is not a faithful model of what the checker
does; it is a ceiling on it.

### 2.2 Universe levels are ground `Nat`s; there is no level judgment

`VExpr.sort` carries a `Nat`.  There is no `VLevel` inductive, no level
substitution, and **no level-equality judgment** — level equality is
`Nat` equality.  `imax` is a computed function (`Setlec.TT.imax`), so
impredicativity of `Prop` is literally its `v = 0` branch, and the `pi`
rule reads `Γ ⊢ A : Sort u → A::Γ ⊢ B : Sort v → Γ ⊢ (A → B) : Sort
(imax u v)`.

This is sound because the denotation happens at a *fixed* level
assignment and everything is unfolded, so every constant is
instantiated at its use site and every level expression in the unfolded
term evaluates to a concrete natural.  Universe polymorphism therefore
lives entirely in the bridge: a polymorphic declaration is denoted once
per ground assignment, and "accepted" means the resulting statement
holds at every assignment.  This is exactly how the existing model
already treats levels (`EnvModel.mem_type` is `∀ φ`), and it makes the
bridge obligation for level comparison trivial: the checker's level
defeq decides equality under *all* assignments, so at a fixed
assignment the two ground levels are literally equal naturals.

The price, stated honestly: the layer cannot express a
universe-polymorphic statement internally.  It does not need to,
because it has no definable constants at all.

Two earlier proposals were considered and dropped: a symbolic `VLevel`
with semantic equality `u ≈ v := ∀ φ, eval φ u = eval φ v` (correct,
but a vestigial `φ` parameter on the whole semantics for no gain once
everything is ground), and an inductive level-equality judgment with
explicit `imax` rules (which would owe a completeness proof against the
checker's `leqCore`/`imaxRules`).  Ground `Nat` beats both.

### 2.3 All conversion is object-level `Eq`

There is exactly one judgment, `HasType Γ e A`.  Every conversion rule
of the checker — β, ζ, η, structure η, unit-like η, K, ι, projections,
proof irrelevance, quotient computation — is a *typing* rule concluding

```
Γ ⊢ prf : eqE T lhs rhs
```

and a single rule, `conv` (equality reflection), turns such a proof
into a type change:

```
Γ ⊢ t : A     Γ ⊢ p : eqE T A B
-------------------------------
           Γ ⊢ t : B
```

Two payoffs:

* **soundness is one induction.**  `⟦eqE T a b⟧ = eqv ⟦a⟧ ⟦b⟧` is the
  truth-set of `⟦a⟧ = ⟦b⟧`, so *inhabitation is the equation*.  There
  is no mutual typing/equality induction and no fixpoint tangle of the
  "defeq mentions typing, typing mentions defeq" kind that a term-level
  definitional-equality judgment forces (cf. lean4lean's `IsDefEq`,
  where typing is the diagonal `IsDefEq Γ e e A`);
* it enshrines extensionality, which is what the target theory has
  anyway (`DESIGN.md`, "The model": propositional and definitional
  equality coincide and are plain set equality).

`eqE` is a *syntactic former*, not a constant applied to three
arguments.  That is what keeps every equational rule premise-free in
the type: `⟦eqE T a b⟧` reads only `a` and `b`, so no
`⟦T⟧ ∈ univ u`/`⟦a⟧ ∈ ⟦T⟧` side conditions are needed to β-reduce an
`Eq`-valued λ-tower.  (Were `Eq` a constant with the usual lam-tower
value, every equational rule would carry three extra membership
premises, i.e. three extra bridge obligations.)

Proofs of equations have no structure: the single constant `VExpr.prf`
inhabits every derivable equation, which is harmless because `eqE _ _ _`
is always a `Prop` and proof irrelevance is a rule.

**Observation for a future simplification.**  The type slot `T` of
`eqE` is *semantically inert* — soundness never reads it — so the
equational rules leave it unconstrained, and hand-written derivations
must annotate it.  Dropping the slot entirely (making the layer's
equality heterogeneous) would be sound and would make the bridge
obligation slightly weaker.  It was kept so that the bridge's
denotation of `@Eq A a b` is transparently `eqE A a b`.

### 2.4 Rules carry exactly the premises soundness consumes

The bridge direction is "checker accepts ⇒ derivation exists", so every
extra premise is an extra bridge obligation.  Accordingly `refl` has no
premise at all, `lam` does not require its domain to be a type, `beta`
does not require the body to be typed, and the `eqE` type slot is never
constrained.  This is a deliberate discipline, not laziness: a rule
that is easier to *apply* is a bridge that is easier to *build*.

## 3. The syntax

```
BConst := nat | natZero | natSucc | natRec
        | punit | punitUnit | punitRec
        | psigma | psigmaMk | psigmaFst | psigmaSnd
        | empty | emptyRec
        | quot | quotMk | quotLift | quotInd | quotSound
        | propext | choice

VExpr  := bvar i | sort n | const c us
        | app f a | lam ty body | pi ty body | letE ty val body
        | eqE ty lhs rhs | prf
```

Differences from `Setlec.Expr`, each deliberate:

* **de Bruijn indices only** — no `fvar`; the local context is an
  explicit `List VExpr` in the judgment, so leaves need no annotation.
* **`letE` is present.**  The checker currently zeta-expands `let`
  before storage, but that pass is scheduled for removal (task #117),
  after which stored terms carry `letE` and the bridge has to type
  them.  See §5 for the rule shape.
* **no `proj`** — projections denote to applications of `psigmaFst` /
  `psigmaSnd`, or, for modeled and directly-installed structures, to
  the projection functions of the unfolded model.  This is exactly what
  `annotateProjElim` / `annotateProjRec` already do inside the checker.
* **no `lit`** — deferred, see §7.
* **no named constants and no environment** — see §2.1.

Two constants of the checker's basis are *absent because they are
derivable*, and both derivations are mechanized in
`Setlec/TT/Examples.lean`:

* **`Eq.rec`** (`eqRec_derivable`): transport is the identity, so
  `fun A a M m b h => m` has the recursor's type.  The step that makes
  it work is `congrEq` — it retypes the canonical proof `prf : a = a`
  as a proof of `a = b`, after which proof irrelevance identifies it
  with `h` and two `congrApp`s move the motive.
* **`PSigma'.rec`** (`psigmaRec_derivable`): the minor premise applied
  to the two projections has the right type once the subject is
  converted along structure η.

Dropping them removes the two most index-heavy dependent types from
`BConst.type`.  Note that `congrEq` was **discovered by attempting the
`Eq.rec` derivation** — without it the layer could not retype an
equality proof along an equation between its own sides, and `Eq.rec`
would not be derivable.  This is the kind of gap the design stage is
for.

`Empty` is deliberately **level-polymorphic** (`Empty.{u} : Sort u`,
interpreted as `∅` at every level, which `empty_mem_univ` supports), so
one constant covers both Lean's `Empty : Type` and `False : Prop`.
This matches the standing decision that `Empty` is a basis type modeled
by the empty set, and it makes the consistency corollary
input-independent.

## 4. The rules

Structural:

| rule | shape |
|---|---|
| `bvar` | `Γ[i]? = some A ⇒ Γ ⊢ #i : A↑(i+1)` |
| `sort` | `Γ ⊢ Sort u : Sort (u+1)` |
| `const` | `Γ ⊢ c.{us} : BConst.type c us` |
| `pi` | `Γ ⊢ A : Sort u`, `A::Γ ⊢ B : Sort v` ⇒ `Γ ⊢ (A→B) : Sort (imax u v)` |
| `lam` | `A::Γ ⊢ b : B` ⇒ `Γ ⊢ λA.b : ΠA.B` |
| `app` | `Γ ⊢ f : ΠA.B`, `Γ ⊢ a : A` ⇒ `Γ ⊢ f a : B[a]` |
| `letE` | `Γ ⊢ ty : Sort u`, `Γ ⊢ val : ty`, `Γ ⊢ body[val] : B` ⇒ `Γ ⊢ (let ty := val; body) : B` |
| `eqType` | `Γ ⊢ eqE T a b : Sort 0` |
| `conv` | `Γ ⊢ t : A`, `Γ ⊢ p : eqE T A B` ⇒ `Γ ⊢ t : B` |

Equivalence and congruence (all conclude `Γ ⊢ prf : …`):

| rule | shape |
|---|---|
| `refl` | ⇒ `eqE T a a` |
| `symm` | `eqE T a b` ⇒ `eqE T' b a` |
| `trans` | `eqE T a b`, `eqE T' b c` ⇒ `eqE T'' a c` |
| `congrApp` | `eqE T f f'`, `eqE T' a a'` ⇒ `eqE T'' (f a) (f' a')` |
| `congrLam` | `eqE T A A'`, `A::Γ ⊢ eqE T' b b'` ⇒ `eqE T'' (λA.b) (λA'.b')` |
| `congrPi` | `eqE T A A'`, `A::Γ ⊢ eqE T' B B'` ⇒ `eqE T'' (ΠA.B) (ΠA'.B')` |
| `congrEq` | `eqE T a a'`, `eqE T' b b'` ⇒ `eqE T'' (eqE S a b) (eqE S' a' b')` |

Core computation:

| rule | shape |
|---|---|
| `beta` | `Γ ⊢ a : A` ⇒ `eqE T ((λA.b) a) (b[a])` |
| `zeta` | ⇒ `eqE T (let ty := val; body) (body[val])` |
| `eta` | `Γ ⊢ f : ΠA.B` ⇒ `eqE T (λA. f↑ #0) f` |
| `funext` | `Γ ⊢ f : ΠA.B`, `Γ ⊢ g : ΠA.B'`, `A::Γ ⊢ p : eqE T (f↑ #0) (g↑ #0)` ⇒ `eqE T' f g` |
| `proofIrrel` | `Γ ⊢ P : Sort 0`, `Γ ⊢ h : P`, `Γ ⊢ h' : P` ⇒ `eqE P h h'` |

Basis computation:

| rule | shape |
|---|---|
| `natRecZero` | ⇒ `eqE T (Nat.rec M z s 0) z` |
| `natRecSucc` | ⇒ `eqE T (Nat.rec M z s (succ n)) (s n (Nat.rec M z s n))` |
| `punitRecUnit` | ⇒ `eqE T (PUnit.rec M m unit) m` |
| `punitEta` | `Γ ⊢ x, y : PUnit.{u}` ⇒ `eqE (PUnit.{u}) x y` |
| `psigmaFstMk` | ⇒ `eqE T (fst (mk a b)) a` |
| `psigmaSndMk` | ⇒ `eqE T (snd (mk a b)) b` |
| `psigmaEta` | `Γ ⊢ p : PSigma' A B` ⇒ `eqE (PSigma' A B) p (mk (fst p) (snd p))` |
| `quotLiftMk` | ⇒ `eqE T (Quot.lift A r B f h (Quot.mk a)) (f a)` |

(The basis rules carry the typing premises of their subterms, which is
exactly what the collapsed `app_lamC` needs to fire — see §6.)

### 4.1 The checklist: every checker capability, and where it lands

| checker capability (`Setlec/Kernel/Core.lean`) | in the layer |
|---|---|
| syntactic equality `a == b` | `refl` |
| β (`whnfCoreBody` `.app`) | `beta` |
| ζ (`whnfCoreBody` `.letE`) | `zeta` + the `letE` typing rule |
| δ (`unfoldDefinition`, incl. theorem values) | **not a rule** — the denotation unfolds (§2.1) |
| ι, basis `Nat` | `natRecZero`, `natRecSucc` |
| ι, basis `PUnit` | `punitRecUnit` |
| ι, basis `PSigma'` | derived (`psigmaRec_derivable`) |
| ι, basis `Quot.lift` | `quotLiftMk` |
| ι, basis `Quot.ind` | `proofIrrel` (the motive is a `Prop`) |
| ι, basis `Eq.rec` | derived (`eqRec_derivable`) |
| ι, modeled recursors (incl. indexed, mutual, nested-aux) | derivable after unfolding `T._model`; **bridge obligation**, see §8 |
| projection reduction (`.proj` on the pinned pair) | `psigmaFstMk` / `psigmaSndMk` |
| projection functions of modeled / direct structures | β + ι of the unfolded model |
| function η (`etaCert`) | `eta` |
| structure η (`structEtaCert`, modeled) | `psigmaEta` after unfolding; bridge obligation |
| pair η (`pairEtaCert`, pinned `PSigma'`) | `psigmaEta` |
| unit-like η (`structUnitCert`, modeled) | `punitEta` / `proofIrrel` after unfolding; bridge obligation |
| unit-like (`isUnitLikeTy`, pinned `PUnit`) | `punitEta` |
| **rule K** (`majorToCtor`) | `proofIrrel` — K's guard is `nF == 0 && piResultIsProp`, so both sides are proofs of a `Prop`.  **No K rule is needed.** |
| proof irrelevance (`proofIrrel`) | `proofIrrel` |
| ∀-congruence, λ-congruence | `congrPi`, `congrLam` |
| app congruence, `defeqSpine` | `congrApp` (iterated) |
| `proj` congruence | `congrApp` (projections are applications here) |
| `const ≡ const` with equivalent levels | `refl` (levels are ground, hence identical) |
| `sort ≡ sort` with `Level.isEquiv` | `refl` (ditto) |
| `fvar ≡ fvar` by de Bruijn level | `refl` |
| level defeq (`leqCore`, `imaxRules`) | `Nat` equality; **no judgment** (§2.2) |
| `propext` | the `propext` constant, in primitive (`Iff`-free) form |
| `Classical.choice` | the `choice` constant, in primitive (`Nonempty`-free) form |
| `Quot.sound` | the `quotSound` constant |
| Nat literal ↔ constructor, `reduceNat` (12 GMP ops), String-literal expansion | **DEFERRED**, see §7 |

Things the checker positively *declines* (custom axioms, unsupported
literal ops without their pins, nested-aux `.inert` rules) need no rule:
a decline is not an acceptance.

### 4.2 What the layer has that the checker does not

Being an upper bound, the layer is strictly stronger in at least these
places, all of them harmless:

* `funext` — the checker has no such rule at all; the layer needs it to
  prove an equation at a `Π` type from pointwise equality (and the
  model supports it, `eq_of_mem_piC_app_eq`).
* structure η on the pinned `PSigma'` — the checker's `PSigma'` is
  deliberately η-*inert* (task #61); the layer's `psigmaEta` is
  unrestricted, which is what makes every modeled structure's η law
  derivable after unfolding.
* `Empty` at every universe level.
* unfolding of modeled inductives, `opaque`s and the trust family
  (§2.1).
* equality reflection at *any* `eqE`, including heterogeneous uses,
  because the `eqE` type slot is unconstrained.

## 5. `letE`: why the substituting rule

The rule types the body with the value **substituted**:

```
Γ ⊢ ty : Sort u    Γ ⊢ val : ty    Γ ⊢ body[val] : B
----------------------------------------------------
      Γ ⊢ (let _ : ty := val; body) : B
```

plus a premise-free ζ equation `eqE T (let ty := val; body) (body[val])`
— premise-free because the *interpretation* of a `let` is literally the
interpretation of its ζ reduct.

The alternative of opening the body with an **opaque variable**
`x : ty` is provably too weak: real streams need the value's
definitional content inside the body (recorded finding, task #79 —
opaque-fvar let bodies reject real streams).  It would therefore fail
the "strong enough to derive everything the checker accepts" test,
which is the sharp risk of this whole project.  The third option —
contexts carrying definitions `Γ, x : A := v` with ζ as a
context-lookup rule — is more faithful to the checker's *lazy* zeta,
but reintroduces exactly the context machinery §2.1 removes.

The substituting rule is adequate despite the checker being lazy
because the layer is non-algorithmic: eager substitution costs only
term size, and every lazy-ζ step the checker performs is recovered from
the ζ equation plus `trans` and congruence.  The bridge for task #117
is then straightforward — the checker's on-demand unfolding of a
let-bound local maps to ζ-`Eq` plus transitivity, with no need for the
layer to mirror the checker's laziness.

**Congruence for `letE` is not primitive.**  It is `zeta`, `trans` and
`symm zeta` around a proof that the two ζ reducts agree, which is the
only shape any consumer needs — the checker itself ζ-reduces both sides
before comparing them.

## 6. The semantics

`interp V ρ : VExpr → V` (`Setlec/TT/Semantics/Interp.lean`) with
`ρ : Nat → V`.  Three properties worth naming, each a payoff of the
design:

* **It is total.**  The checker-side `interpExpr` is `Option`-valued and
  comes with the auxiliary truthfulness predicate `AnnotOk`, because it
  interprets *arbitrary* `Expr`s and must reconstruct at every binder
  the fibre/membership facts that a typing derivation would have
  supplied.  Here the derivation supplies them, so the interpretation
  is a plain function and **`AnnotOk` has no counterpart at all**.
* **It has no level-assignment parameter** (§2.2): `⟦Sort n⟧ = univ n`.
* **`eqE`'s type argument is not read**: `⟦eqE T a b⟧ = eqv ⟦a⟧ ⟦b⟧`.

`⟦Eq⟧` as the truth-set is exactly what equality reflection needs, and
it works unchanged under the newly-landed collapse model (level-free
`piC`/`lamC`, `pcol`): `eqv` is `Derive/Pt.lean`'s `truthVal (x = y)`,
`mem_eqv` turns inhabitation into set equality, and nothing in the
collapse touches it.

### The substitution metatheory is two lemmas

`interp_liftN` and `interp_inst`.  That is the whole of it.  For
contrast, lean4lean's `Theory/VExpr.lean` is ~800 lines and **123
theorems** of substitution boilerplate — about a third of its
declarative layer, and 10× the size of its typing judgment — because
its metatheory is *syntactic* (Church–Rosser, unique typing, weakening,
inversion) and every step has to commute lifts and substitutions past
each other.  Mario even wrote the naive `liftN`/`inst` API and *then* an
explicit-substitution `Lift`/`Subst` algebra on top, because the naive
one did not compose.  Our only metatheorem is soundness, which goes
straight to the model, so no syntactic commutation is ever needed.

### The collapse, where it shows

Two places in `Setlec/TT/Semantics/Value.lean`:

* `psigmaMkV` is the proof point when the joint level is `0` — at
  `Prop` the pair set is a truth value, so a Kuratowski pair could not
  inhabit it (`sigmaSet_zero`);
* `quotIndV`, `quotSoundV`, `propextV` and `emptyRecV` are *just* the
  proof point, because their whole λ-tower ends in a `Prop` and
  therefore collapses.

Structure η for `PSigma'` is sound at *both* levels precisely because
`psigmaMkV` collapses: at level `0` both the subject and the reassembled
pair are `pt`; above it the Kuratowski pair is literally rebuilt.

### The app rule's argument fact (the AppSlot/ChainSlots payoff)

The declarative `app` rule has `Γ ⊢ a : A` as a premise, so soundness
gets `⟦a⟧ ∈ ⟦A⟧` by induction hypothesis.  This is exactly the fact the
checker currently has to re-establish at *every* reduction site,
because the collapsed `app` is non-invertible.  Concretely, the
checker-side `AnnotOk` clause for an application is

```
AnnotOk f ∧ AnnotOk a ∧ ∃ vf va A B, ⟦f⟧ = some vf ∧ ⟦a⟧ = some va ∧
  vf ∈ˢ piC A B ∧ va ∈ˢ A
```

— the existential package that the annotate pass establishes and every
reduction proof re-consumes.  In the layer that package *is* the
premise.  Correspondingly the β case of soundness is three tactic
lines: `app_lamC` fires on domain membership alone under the collapse,
and the membership is the IH.

## 7. Deferred: literal computation (a known future obligation)

**Not built in this pass, by direction, and named here so that it is not
discovered after the soundness proof.**

The checker accepts `Nat.add 12345 67890 = 80235` through certified GMP
fast paths (`reduceNat`, and the pinned `add/sub/mul/pow/beq/ble` plus
the WF family `div/mod/gcd/land/lor/xor/shiftLeft/shiftRight/log2`), and
it expands `String` literals to their constructor form at three sites.
Deriving those from `Nat`'s ι rules alone would be astronomically large
derivations, so the layer will eventually need **built-in literal
rules**: a `lit` constructor in `VExpr`, built-in constants for the
pinned operations, and computation rules `natAdd (lit a) (lit b) ≐
lit (a+b)` with the arithmetic done in the metalanguage's own `Nat`.
They are justified in the model by exactly the certificates the checker
already carries (`NatOpsOk`, `DivModOk`), so the work is bounded and
known; it simply is not this pass.

Until then the bridge cannot denote a declaration whose acceptance went
through a literal fast path.  This is the single largest coverage gap
of the layer as it stands.

## 8. Where the work relocates (bridge obligations, not done here)

The layer does not shrink the total verification effort; it changes its
*shape*, from model reasoning to rule application, with a bridge in
between.  Say that plainly rather than overselling it.  Both paths
coexist until the bridge is complete, and **no existing model proof
should be deleted** on the strength of this layer.

The denotation function from a real `Env` + `Expr` into `VExpr` now
carries the whole burden:

1. **Full unfolding terminates** (kernel-level definitions are
   non-recursive — recursion goes through recursors or `WF.fix` — over
   a well-founded environment), though it can blow up in size.
   Irrelevant for a non-algorithmic spec, but the denotation must be
   defined by well-founded recursion on the environment.
2. **The principal obligation**: when the checker fires an installed ι
   rule for an opaque `T.rec` *without knowing `T`'s model*, the bridge
   must show that the fired rule is derivable after unfolding.  The
   install-time model checks (`checkIotaThm`/`checkIotaThmN`, and the
   `RecRulesOk` total-λ-equality contract of task #58) are exactly what
   makes that provable.
3. The same for the capability laws: `caps.eta` comes from a checked
   `T._model.eta` theorem, `caps.unitlike` from `T._model.unitlike`;
   after unfolding, each becomes an equation the layer must derive from
   `psigmaEta`/`punitEta`/`proofIrrel`.
4. Literal fast paths — §7.
5. Level comparison: trivial, as noted in §2.2.

## 9. Status

Landed on `feat/74-tt-layer`, ~1500 lines:

* `Syntax`, `Subst`, `Const`, `Judgment`, `Examples` — the
  checker-independent layer;
* `Semantics/{Value, Interp, ConstOk, Soundness, Consistency}` — the
  interpretation, `bval_mem_type` (every built-in constant inhabits its
  type), `HasType.sound`, and `no_proof_of_empty`.

No `sorry`s; `no_proof_of_empty` depends only on
`propext, Classical.choice, Quot.sound`.  Nothing in the checker
imports the layer, so the checker's behaviour is unchanged by
construction — there is no init-prelude movement to measure, and none
would be meaningful.
