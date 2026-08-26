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

**Delta is not a rule of the type theory, and it is not a `refl`
either: it is an equation between denotations that the invariant
already carries.**  This supersedes the "a delta step becomes `refl` on
the TT side, because `D` already unfolded" formulation of the original
sketch.  The payoff is the same one — the reduction strategy drops out
of the consistency argument — reached with less machinery: no
unfolding, no well-founded recursion on the environment, and no
termination obligation to discharge.

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

## 3. Projections: a gap in the layer, found here and closed

**Recorded because it is the one place the mirroring did not
transpose, and because the fix made the layer smaller rather than
bigger.**

`interpExpr` reads a `.proj` node with the *untyped* `sfst`/`ssnd`.
The layer's `psigmaFst`/`psigmaSnd` were constants **applied to the
pair's type arguments** `A` and `B`.  A `.proj` node does not carry
them; the checker recovers them at use time by whnf-ing the subject's
inferred type.  A denotation that is a function of the expression alone
cannot.  And a *relational* denotation is no escape — the defeq clause
of the fuel induction needs both sides denoted by the same map, or the
two existentials never meet.

`Setlec/TT/DESIGN.md` §3's "projections denote to applications of
`psigmaFst`/`psigmaSnd`" was right for a *modeled* structure, whose
node the checker rewrites away at annotation, and silent about the
**pinned pair**, whose node is first-class by design
(`ProjEntry.native`) and survives into stored terms.  Scale, measured:
188 `proj` records in the preprocessed init-prelude stream, and at
least one in 34 of the committed e2e fixtures.

**Closed on `feat/74-proj-former`** (landed 2026-08-26): `VExpr.proj i
e` carries exactly what the checker's node carries, and
`projFst`/`projSnd` read `A` and `B` off the premise
`Γ ⊢ p : PSigma' A B`.  Same move as the `app` rule, same payoff — the
premise hands soundness the `⟦p⟧ ∈ˢ sigmaSet …` package that the set
model's `AnnotOk` proj clause carries by hand.  One further rule was
needed, `congrProj`: `proj` is not an application, so no existing
congruence reaches it and `conv` changes types rather than terms.

The net effect on the primitive set is **negative**: `psigmaFst` and
`psigmaSnd` are `fun A B p => p.i` and left `BConst`, mechanized in
`Examples.lean` beside `Eq.rec` and `PSigma'.rec`.  That asymmetry is
the argument that the former is a primitive rather than an addition —
it derives the constants, and no set of constants derives it, because
only the former can be typed without its type arguments appearing in
the term.

`denote`'s clause is now the plain transpose of `interpExpr`'s, `i < 2`
guard included.

## 4. What is proved, and what the remaining hypotheses are

Stage 1 (the denotation, the invariant, the fold) and the opening of
stage 2 are proved, `sorry`-free and on
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
  consistency corollary, through `Setlec.TT.no_proof_of_empty`;
* `checkSoundTT` — the mutual fuel induction, with its **fuel-zero**
  case proved outright and its step named (`Setlec/TTVerify/Claims.lean`);
* `hasType_app_inv` / `hasType_proj_inv` — the two inversions the
  threaded claims need to feed their own recursion (§6);
* `denote_mono` — **denotations survive environment extension**
  (`Setlec/TTVerify/Extend.lean`).  This is the workhorse every install
  step needs, in the same place the set model needs its
  `Extend/Transport` family, and it is one lemma here rather than a
  family because nothing in this hierarchy mentions `AnnotOk` or a
  set-theoretic interpretation.

Two hypotheses remain open, both named `Prop`s rather than `sorry`s so
that every consumer of an unproved step is visible in the source:

* `CheckDeclTT` — "checking one declaration preserves the derivation
  model", the transpose of `checkDecl_sound`;
* `CheckStepTT` — the `succ` case of the fuel induction, the
  clause-by-clause transpose of `Setlec/Model/Core/*`.

`CheckDeclTT` will be discharged *through* `CheckStepTT`; they are
separate because the declaration checker and the core knot are separate
inductions on the set-model side too.

Note where the set theory enters: **nowhere in `EnvTT`**.  The
invariant is purely derivation-level; a `SetTheory V` instance is
needed only at `no_constant_of_Empty_TT`, where the layer's own
consistency theorem turns the pinned valuation of `Empty` into
uninhabitation.

### The traversal invariants (one acted on, one still a candidate)

Two facts in `Setlec/TTVerify/Claims.lean` are properties of the
*traversal* rather than things each node earns, and the difference
between them is worth keeping straight.

* **Well-typedness: threaded, as of §6.**  The reduction and defeq
  claims take `HasType Δ ⟦e⟧ A` as a hypothesis and hand the reduct's
  typing back as a conclusion.  See §6 for the measurement that forced
  this and for the evidence that the recursion can actually feed
  itself.
* **`CtxOk`: still a hypothesis at every node.**  It is likewise an
  invariant — the context correspondence does not change as the
  traversal descends into a subterm at the same depth — but nothing
  measured says it costs anything, and unlike well-typedness it is not
  a fact the checker computes at run time.  Left as it is; noted so
  that a future reader sees it was considered.

### The direct-install hypothesis, and what it costs

Stage 2's step is stated for `directStructsEnabled = false`
(`Setlec/Kernel/Direct.lean`, and the top-level `DESIGN.md` section
"The master switch, and why it defaults on").  A directly installed
structure has no `_model` artifact and the denotation of a stored
inductive goes through exactly those artifacts.

**The switch defaults on.  So say the consequence plainly: the TT
consistency result is vacuous for the configuration we actually
ship.**  A reader who finds a conditional theorem here must not
conclude that it covers the binary — it does not, and no amount of
gate-green reporting changes that.

This is acceptable, for exactly two reasons and no others.

1. It is **explicitly staged**.  The hypothesis is a named `Prop`
   argument of every theorem that depends on it, not a hidden side
   condition, so the restriction is visible at each use site.
2. The **set model still covers the full shipped configuration**,
   direct install included — task #82 landed with `checkDecl_sound`
   covering the direct clause, and nothing in task #119 weakens,
   replaces or deletes any of it.  So we lose nothing today: the set
   model remains the shipped guarantee while the TT route is built up
   over a sub-configuration.

Since 2026-08-26 the switched-off configuration is at least
*exercisable*: `tests/build-direct-off.sh` builds a second binary with
the constant flipped, without mutating the tree.  That does not make
the theorems cover the shipped default — they still do not — but it
means the configuration they do cover is one a reader can run rather
than one that exists only in a proof.

**Exit condition.**  The TT route covers the shipped default only once
one of two things happens: the layer supports directly installed
structures (their tower encoding denotes, as
`Setlec/Model/DirectTower.lean` already interprets it), or direct
install is retired — which is the standing plan the moment the class
earns `eta`/`unitlike` and `lean-inductive-models` stops emitting
artifacts for it (top-level `DESIGN.md`, "Task #82 is complete").
Until then, quoting a TT consistency theorem as a statement about the
binary is a category error.

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

## 6. The certificate tax, and why the claims thread typing

**Recorded here because the investigation that produced it ran on
`diag/cert-tax`, a throwaway branch, and these numbers exist nowhere
else in the repository.**  They are also the reason stage 2 deviates
from a plain mirror of the set-model proof, so they belong to this
argument rather than to a performance appendix.

### The tax is one call

Measured by an isolating mask over the whole `Init` cone:

| | cost |
|---|---|
| per-argument re-check in `inferSpineI` | **288 s** |
| every other certificate family, summed | 4 s |
| total tax | 292 s |

That one call is **98.6 %** of it.  The site is
`Setlec/Kernel/CoreI.lean:1534` (the certificate at 1545–1547 and its
post-whnf twin at 1554–1556); the spec-side twin is the `.app` clause
of `inferBody`, `Setlec/Kernel/Core.lean:1495`.  `--yolo` is a literal
alias for `SETLEC_NO_PROOF_CERTS`, so the whole ~39× certified/yolo gap
is certificates and nothing else.

**What that call establishes is `⟦a⟧ ∈ˢ ⟦A⟧` at every application
node** — precisely `AnnotOk`'s app clause — and it exists *only*
because `AnnotOk` is a **conclusion** of the inference claim rather
than a hypothesis carried along.  The information is already present at
the call site; the set-model architecture has no channel to carry it.
A typing judgment is that channel, which is the same observation
`HasType.app`'s docstring makes from the other side.

**The reference kernels perform this check too — once per
declaration, never inside reduction.**  The official kernel's
`m_infer_type[infer_only]` is a two-element cache array; lean4lean's
`isDefEqCore` docstring states the justification outright.  Doing it on
every reduct is our artifact, not a fidelity requirement.

### Per-call verdicts

| certificate | verdict | note |
|---|---|---|
| app-argument re-check (`inferSpineI`) | **replaceable**, high confidence | the 98.6 % |
| iota telescope certifications | replaceable | |
| structure-eta, `projCert` | replaceable | and measured free anyway |
| plain-rule parameter comparison | **needed**, cheap | |
| canonical-index `defEqList` | **needed**, cheap | |
| beta re-check | **needed** *under the current rule set* | the qualifier is load-bearing; see below |

The last two are worth their keep for a reason that inverts the usual
intuition: removing them made the run *slower*, because they
short-circuit reduction.

### What this changes here

The claims of `Setlec/TTVerify/Claims.lean` **thread the typing
hypothesis from the start** rather than re-deriving membership at each
node.  The shape is: `⊢ ⟦e⟧ : A` and `whnf e = e'` give
`⊢ prf : eqE _ ⟦e⟧ ⟦e'⟧`, and `⊢ ⟦e'⟧ : A` follows by `conv` — subject
reduction is free in a layer whose conversion is equality reflection,
which is the entire point.

Stating it this way now is the cheap move: an extra hypothesis makes
each claim *weaker*, so nothing gets harder to prove, and when the
checker eventually gains an infer-only mode and drops the app-argument
check, that is a change to the checker rather than a retrofit of this
induction.  Retrofitting later is the expensive direction.

**The threading is not assumed to work — it is de-risked.**  A
recursion that carries a typing must hand each subterm a typing of its
own, and the layer has no inversion principle.  So
`Setlec/TTVerify/Inversion.lean` proves exactly the two the checker's
own recursion needs — the head and argument of an application, the
subject of a projection — each one induction with two interesting cases
(`app`/`proj*`, and `conv`, which does not change the subject) and a
catch-all closed by constructor disjointness.  That is a bounded,
named departure from the layer's "no syntactic metatheory" discipline,
and it is in `Setlec/TTVerify/*` rather than `Setlec/TT/*` to keep it
marked as a bridge need.

### The beta clause: the certificate is needed under the current rule set

The investigation left the beta re-check as its one **unclear** verdict,
leaning needed.  The bridge sharpens that to **needed under the current
rule set**, for a proof-level reason rather than a measurement — and
the qualifier is not hedging, it is the whole content of the next
paragraph but one.

`HasType.beta`'s premise is `Γ ⊢ a : A` at *the λ's own annotation*.
Inverting a typed redex `⊢ (λA.b) a : C` yields
`⊢ λA.b : Π A₀ B₀` and `⊢ a : A₀` — the ambient domain, not the
annotation (`Setlec/TTVerify/Inversion.lean`).  The premise is not
decoration: soundness consumes it as the domain membership that fires
`app_lamC`.

What closes the gap today is the checker's own beta certificate — infer
the argument's type, compare it definitionally with the annotation —
which the inference and defeq claims turn into `⊢ ⟦a⟧ : ⟦ta⟧` and
`Deq Δ ⟦ta⟧ ⟦A⟧`, hence `⊢ ⟦a⟧ : ⟦A⟧` by `conv`.  So this certificate
is load-bearing *for the bridge*, not merely plausible-looking.  No
performance cost attaches to keeping it: it is free once the
app-argument check is gone.

#### OPEN: derivable Π-injectivity (tracked separately — do not close this)

Whether the premise could be weakened instead, by a lemma

> for every derivation of `Deq Δ (Π A B') (Π A₀ B₀)`, a derivation of
> `Deq Δ A A₀` exists,

is an **open metatheory question about this layer**, and a task is open
for it.  Nothing above answers it.  The verdict recorded here is
"needed *under the current rule set*" precisely so that the question
stays open; a reader who takes it as settled will drop the task, and it
is the question that decides whether a cert-skipping run can ever be
the *verified* mode.

**In particular, semantic Π-injectivity being false under the
domain-relative collapse is not evidence either way.**  That is a
statement about what *holds in the model*; the lemma above is a
statement about what *the rules generate*.  Derivable equations are a
strict subset of true ones, and that asymmetry is the entire reason
this layer is an upper bound in one direction and not the other
(`Setlec/TT/DESIGN.md` §2.1) — a false-in-the-model principle can still
be underivable, which is what would need proving, and a true-in-the-
model one can still be underivable too.  The same distinction is what
made the task #100 countermodel irrelevant to derivability: that
countermodel needs `⊢ Prop : ∀ p : Prop, p`, and no such derivation
exists.

An earlier revision of this section asserted that semantic falsity
settled it.  It does not, and the error is recorded rather than quietly
fixed because it is an easy one to make twice.

The practical upshot does not depend on the answer, which is why this
is comfortable to leave open: performance is unaffected either way
(beta is free once the app-argument certificate goes).  Only "validate
`--yolo` literally" turns on it.

## 7. The substitution stack

`CheckStepTT` has a single bottleneck that every interesting clause
runs through — `app`, `beta`, `zeta`, every iota rule:

> **`denote` commutes with instantiation.**  If
> `denote (d+1) (body.instantiate1 (.fvar d n ty)) = some B` and
> `denote d a = some x`, then
> `denote d (body.instantiate1 a) = some (B.inst x)`.

The checker's `infer` on `.app f a` returns the `Expr` `B.instantiate1
a`; `HasType.app` concludes at `(⟦B⟧).inst ⟦a⟧`; those must be the same
`VExpr`.  The model's counterparts are `interp_beta` and
`interp_substFvarAt` (`Setlec/Model/Subst.lean`), and the `Expr`-side
machinery both lean on — `substFvarAt`, `shiftFrom`,
`fvarsBelow_instantiate1` and friends — is in
`Setlec/Verify/{Shift,Subst}.lean`, which this hierarchy may import.

### Landed: the shift lemma (`Setlec/TTVerify/Shift.lean`)

Its prerequisite is done: `denote_lift`, the transpose of
`interp_lift`, with `denote_shiftFrom` as the generalization and
`denote_weaken_top` as the induction step.  Three things came out of
it that were not visible from the analysis.

**1. The statement deviates, and had to.**  `interp_lift` concludes a
literal *equation* — `interpExpr D ρ' e = interpExpr p ρ e` — because
`interpExpr` reads a free variable through `ρ` and never through the
depth, so the valuation absorbs it.  `denote` reads
`.bvar (d - 1 - i)`, which is depth-relative, so the transpose is

```
Expr.fvarsBelow p e → p ≤ D →
  denote D e = (denote p e).map (·.liftN (D - p))
```

Deliberate deviation, recorded in the module header so a reader
checking the transposition line by line does not stop there and wonder
what broke.

**2. The generalization closed exactly as predicted.**  The cut `d - p`
is incremented by the binder clause to `(d - p) + 1`, which is what
`VExpr.liftN` does to its own cut — so the two sides stay in step.  The
fact that makes it work is the one already noted: the freshly opened
variable denotes `.bvar 0` at *every* level, so only outer variables
move, and by exactly one.  One hypothesis had to be added that the
analysis missed — `Expr.fvarsBelow d e`, without which the `fvar` case
is false at `p = d` — but that is a hypothesis the model's version
carries too.

**3. Two findings that were not in the analysis at all.**

*`EnvTT` needs a field `EnvModel` does not: `cval_closed`.*  The
`.const` clause of the shift lemma needs a constant's denotation to be
invariant under lifting, i.e. **closed**.  `interpExpr` owes nothing
here because `val n ψ : V` is a set with nothing in it to lift.  This
is the exact mirror image of the saving in §2: `denote` needs no
free-variable valuation because the opened binder *is* a variable, and
the price is that a constant's denotation is a *term* with no loose
variables.  It is the syntactic shadow of `val_params`, and it is
recorded as such on the field.  Supporting facts:
`Setlec/TTVerify/VClosed.lean`.

*`denote` is now structural at `let`, and the earlier choice is
withdrawn.*  §2 said a `let` denotes to its zeta reduct, mirroring
`interpExpr`.  That forced `denote` to *perform a substitution*, and
the shift lemma's `letE` case then needed lifting-commutes-with-
instantiation, which needs lifting-commutes-with-lifting — i.e. the
syntactic-substitution swamp `Setlec/TT/DESIGN.md` §6 is proud of
avoiding, reappearing one layer down in the bridge.  So `denote` now
emits `VExpr.letE` and every clause maps a constructor to a
constructor; the shift lemma's `letE` case is structural and needs no
commutation lemma at all.  A consumer wanting the reduct uses
`HasType.zeta`, which is premise-free and exists for exactly this.

The general principle, worth keeping: **a structural `denote` is what
keeps the bridge's substitution metatheory small.**  Whenever a clause
is tempted to compute, the cost lands here.

### Next

`denote` commutes with instantiation, mirroring `interp_substFvarAt`
and `interp_beta`, then the clauses of `CheckStepTT` against the
threaded claims of §6.  With `denote` structural, that proof's binder
cases are structural too, and its one interesting case — a free
variable at the substitution point — is discharged by `denote_lift`,
because `VExpr.inst`'s built-in `liftN k` on the substituend is exactly
the depth shift (§7's arithmetic note above).
