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

`EnvTT env` is `EnvModel env` field for field, **with one documented
exception** — `cval_closed`, which has no counterpart at all and is not
an incidental well-formedness condition; see the row and §7:

| `EnvModel` | `EnvTT` |
|---|---|
| `val : ConstVal V` | `cval : TConstVal` |
| — | `cval_closed` — **the one addition**; the price of the row below it |
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
* **`denote` is structural — every clause maps a constructor to a
  constructor**, including at `let`.  This is a *principle*, not a
  convenience, and it is the one to preserve if any clause is ever
  tempted to compute:

  > **A structural `denote` is what keeps the bridge's substitution
  > metatheory small.**

  The `letE` clause is where it was decided, and by withdrawing the
  opposite choice.  This document originally said a `let` denotes to
  its zeta reduct, mirroring `interpExpr`; that made `denote` *perform
  a substitution*, and §7's shift lemma then needed lifting to commute
  with instantiation, which needs lifting to commute with itself — the
  syntactic-substitution swamp `Setlec/TT/DESIGN.md` §6 is proud of
  avoiding, reappearing one layer down in the bridge.  A `let` now
  denotes to `VExpr.letE`, and a consumer wanting the reduct gets it
  from `HasType.zeta`, which is premise-free and exists for exactly
  this.  See §7 for what that bought, in lemmas.
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
  constant for `Nat.add`.  The bridge's obligation at a certified fast
  path is: denote the checker's own certificate for that operation
  (which `EnvTT` carries, by the same mechanism that carries the
  `_model` iota theorems), instantiate it at numerals, and hand the
  resulting `Deq` equations to `numeral_add` and friends.

  **The instantiation is done by the theory, not by a substitution
  lemma** — write it this way and do not reach for `HasType`
  substitution here.  `NatOpsOk` quantifies over two free-variable
  *values*, so its transpose is a `Deq` in context `[natT, natT]`,
  while `Setlec/TT/Nat/*` wants it closed at numerals.  The recipe:

  1. apply `lam` twice — it carries **no domain premise**, so this
     costs nothing — abstracting the equation into a closed
     λ-λ-equation;
  2. apply the `app` rule twice, at `numeral a` and `numeral b`.  The
     rule's own `B.inst a` performs the instantiation **object-level,
     in the type**;
  3. two `symm`s restore the `prf` subject, the `eqE` slot being inert.

  The theory internalizes its own substitution through abstraction,
  application and the inert slot.  This is worth knowing beyond the
  `Nat` case: whenever a `Deq` has to move from an open context to a
  closed instance, prefer this route.

  `String` literals need nothing: `strLitToConstructor` is finite and
  explicit.
* **Modeled iota, eta, unit-like, K.**  Not a risk: the `_model`
  theorems are stream declarations the checker *accepted*, so
  `EnvTT.has_type` already supplies a derivation of each by the time
  any later declaration fires the rule.  Firing is instantiation plus
  `trans`.  A propositional equality suffices because conversion in
  this layer is equality reflection.  K needs nothing at all — its
  guard makes it proof irrelevance (the #74 finding).

## 6. The certificate tax, and the fact that explains it

**The headline of this section is one fact about the layer.**  It was
discovered three times, in three unrelated investigations, before being
recognised as one thing; it is stated here first so that the fourth
time is not a discovery.

> **Premises are supplied where the rule fires.**
>
> The layer's rules state their typing premises at *annotations and
> inferred domains* — `HasType.beta` wants the argument at the λ's own
> annotation, `HasType.app` at the domain of the function type used in
> that application — and its equational rules are **premise-free**
> (`Setlec/TT/DESIGN.md` §2.4), so an equation carries no typing
> information at all.  Together: every typing premise must be
> established at the point where its rule is applied, and **nothing
> carried from elsewhere — an ambient hypothesis, a global invariant, a
> prior check — can substitute for it.**

Three consequences, each of which looked like an independent question:

1. **Subject reduction is refutable here** (not merely underivable):
   "`⊢ t : A` and `Deq t t'` imply `⊢ t' : A`" fails, because equations
   relate typed terms to untypeable ones by design.  See the
   retraction below.
2. **Infer-only mode cannot be justified in this bridge** (task #124),
   so the app-argument certificate — 98.6 % of the tax — is permanent
   *here*.  All four routes to the argument's typing at the inferred
   domain are closed, the last of them because the official kernel's
   own justification *is* subject reduction.  See "Why the certificates
   are structural".
3. **The modeled-iota contract is the fired form, by dominance** (§8):
   the alternative — a closed λ-tower equality — does not avoid the
   typing premises, it defers them to the fire site and adds a
   β-reduction apparatus on top of them.

A fourth consequence, if the reading under "Domain pinning" survives:
the certificate is doing the one thing nothing else can do, which is
why it is the one call that costs.

The measurements below are **recorded here because the investigation
that produced them ran on `diag/cert-tax`, a throwaway branch, and
they exist nowhere else in the repository.**

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

### Per-call verdicts — two columns, not one

**The cert-tax investigation's verdicts answer one question; this
bridge asks a different one, and the two were being conflated
(including by me, until the `iotaCerts` case forced the distinction).**

* *Checker can skip* — the empirical verdict: masked out, the checker
  still reaches the same verdicts.  Evidence: measurement.
* *Bridge can do without* — whether the **proof** can obtain the fact
  another way.  Evidence: the headline fact, plus a clause that
  actually goes through.

They are different properties and they come apart.  The app-argument
re-check is the demonstration: skippable by the checker (the reference
kernels skip it), and **permanent** for the bridge.

| certificate | checker can skip | bridge can do without | status |
|---|---|---|---|
| app-argument re-check (`inferSpineI`) | yes — the 98.6 % | **no** | *established* (four routes closed) |
| beta re-check | yes | **no** | *established* (`propext` refutes the alternative) |
| iota telescope certifications (`iotaCerts`) | yes | **no** | **prediction** |
| structure-eta / unit-like telescope certifications | yes | **no** | **prediction** |
| `projCert` | yes — measured free anyway | **no** | **prediction** |
| plain-rule parameter comparison | no — cheap, short-circuits reduction | no | needed by both, for *different* reasons |
| canonical-index `defEqList` | no — ditto | no | needed by both, for *different* reasons |

The pattern behind the third column, which is itself the falsifiable
part:

> Certificates come in two kinds.  Those that establish **an argument's
> typing at a rule's domain** are permanent for the bridge — that is
> exactly the fact nothing ambient can supply.  Those that perform
> **syntactic matching** (which rule fires, whether the indices agree)
> are needed by checker and bridge alike, but for unrelated reasons:
> the checker to reduce, the bridge to know which contract instance it
> is discharging.

`HasType.psigmaEta` wants `⊢ A : sort u`, `⊢ B : A → sort v`,
`⊢ p : PSigma' A B`; `projFstMk` wants four of the same kind; the iota
contract's telescope hypothesis wants one per argument.  All three are
the same shape as `beta`'s premise, so the headline fact applies to
all three.

**These are predictions, not re-verdicts.**  I have not reached those
clauses.  They carry the same falsifiable status as the `iotaCerts`
one: **if a clause discharges its rule's premises without the
corresponding certificate, the headline fact is wrong**, and that is a
larger event than an easier clause — it would unseat three consequences
and a contract decision.  Report it as a finding before working around
it.

### What this changes here — and what it does not

**Nothing.  The claims stay certificate-only**, mirroring
`Setlec/Model/Core/Claims.lean`.  An earlier revision threaded a typing
hypothesis through them on the argument that this was the path to
removing the app-argument check; that revision is withdrawn, and the
next subsection is why.

### Why the certificates are structural (and task #124 cannot be
### justified here)

The measurement above says the app-argument re-check is 98.6 % of the
tax and that the reference kernels do it once per declaration rather
than per reduct.  The natural conclusion — carry the fact instead of
re-deriving it — **does not work in this layer**, and the reason is a
property of the layer rather than a missing lemma.

Take the app clause in infer-only mode.  The bridge must conclude
`⊢ .app ⟦f⟧ ⟦a⟧ : ⟦B⟧.inst ⟦a⟧`.  `HasType.app` is the only rule with
an `.app` conclusion (up to `conv`, which does not change the subject),
and it demands the argument at **the domain of the function type used
in that application**.  The induction hypothesis for `f` fixes that to
be the checker's inferred `⟦A⟧`.  So `⊢ ⟦a⟧ : ⟦A⟧` is required, on the
nose.  Four routes, all closed:

1. **Re-infer and compare** — the certificate.  This is the one we
   were trying to remove.
2. **Ambient hypothesis plus inversion.**  `hasType_app_inv` yields
   `⊢ ⟦a⟧ : A₀` for *some* domain `A₀` of *some* pi type of `⟦f⟧`.
   Bridging `A₀` to `⟦A⟧` means descending a `Deq` between two pi types
   into the domain — **Π-domain-injectivity, refuted by `propext`**
   (below).
3. **A stronger carried invariant**, e.g. "every app node's argument is
   typed at its function's inferred domain".  Reduction *creates* app
   nodes — beta's reduct is a substitution instance — and the functions
   in them have substituted types, so the invariant would have to be
   preserved by substitution *at the inferred domains*, which is
   route 2 again at every new node.
4. **A global argument**: the declaration was checked once in checking
   mode, and everything reduction sees descends from a well-typed term.
   **This is the official kernel's actual justification, and it is
   subject reduction** — which this layer *refutes*, by design, via the
   premise-free equations of `Setlec/TT/DESIGN.md` §2.4 (see the
   retraction above).

So the certificates are forced by the conjunction of two deliberate
choices: **equations carry no typing** (premise-free rules), and
**computation rules state their premises at annotations and inferred
domains, not at ambient types**.  Together those mean every reduction
rule's typing premise must be supplied where the rule fires.  No
invariant carried from above can substitute for one.

**What this does and does not say about task #124.**  It does *not*
say infer-only mode is unsound — the official kernel runs it and is
sound, its justification living in a framework that *has* subject
reduction.  It says **this bridge cannot justify it**, so adopting it
would be a reduction in what the verification covers, not a free win.
That is a scoping fact for #124 to weigh, not a defect in it; the
performance case is untouched.

And it says something about the shape of any future attempt: a layer
that could justify infer-only would need premise-*carrying* equations,
i.e. subject reduction — the opposite of §2.4.  That is a real trade
(every equational rule gains typing premises, and every one of them
becomes a bridge obligation), and it should be entered deliberately if
ever, not drifted into.

#### Domain pinning, and what the certificate is *for*

One sentence that covers both frameworks, offered as a reading rather
than a result:

> **From the ambient facts you cannot recover which domain a function
> was applied at.  The certificate exists to pin it.**

In this layer, `propext` makes `Π` non-injective, so a `Deq` between
two pi types does not descend to their domains.  In the set model the
domain-relative collapse erases the domain outright at `Prop`
(`lamC A f = pt`), so the function's *value* does not determine it
either.  Different mechanisms, same conclusion, and it explains why the
certificate is the one call that costs 98.6 %: it is doing the one
thing nothing else can do.

If this reading survives contact with the remaining clauses it is the
one-sentence summary of the whole certificate question; if a clause
refutes it, that is worth more than confirming it.  Not investigated
beyond what the clauses show.

#### The trade, stated so the layer is not blamed for it later

**The same property that forecloses infer-only is the one that buys
the layer its advantages.**  Typing here is a *derivation about
syntax*, so an equation transports none of it — which is the whole
obstruction above.  Typing in the set model is `⟦e⟧ ∈ˢ ⟦T⟧`, a property
of the *value*, so it transports along interpretation-equality for
nothing; correspondingly `WhnfClaims` concludes `AnnotOk e'` from
`AnnotOk e` and semantic subject reduction is free there.  That same
intensionality is what makes the layer's substitution metatheory two
lemmas instead of 123 (`Setlec/TT/DESIGN.md` §6) and what makes
`AnnotOk` disappear from this bridge entirely (§2).  Genuine trade, not
a defect.

So **route 4 is available in form on the set-model side and not here**,
and that is worth knowing: it would make the set model the stronger
framework in exactly one place.  Whether it is available in *substance*
is a separate question this note does not settle, and one caveat should
be checked before anyone counts on it: `AnnotOk`'s app clause supplies
the argument in `∃ A B`, i.e. in *some* domain, and pinning that to the
checker's inferred domain needs the function's value to determine its
domain — which the domain-relative collapse defeats at `Prop`, where
`lamC A f = pt` erases it.  That is the same shape as the task #100
countermodel, so the obstruction may be different and weaker there
rather than absent.  Recorded as a lead, not a result.

### The beta clause: the certificate is permanent

The investigation left the beta re-check as its one **unclear** verdict,
leaning needed.  The bridge sharpens that to **needed under every sound
rule set** — an instance of the headline fact, with the alternative not
merely unavailable but *inadmissible*.

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

#### CLOSED, NEGATIVELY: derivable Π-injectivity is inadmissible

The previous revision recorded this as an **open** question and told
the reader not to close it.  It is now closed, in the direction that
makes the certificate permanent: **derivable Π-domain-injectivity is
refuted, and adding it as a rule would be unsound.**

The witness is `propext` — precisely the case the earlier revision was
warned to check, and did not:

* `P₁ := False → False` and `P₂ := Nat → PUnit.{0}` are both `Prop`s,
  since `imax _ 0 = 0`;
* both are derivably inhabited (the identity; the constant function),
  so each implies the other, and four applications of `propext` give
  `Deq [] P₁ P₂`;
* domain-injectivity would then give `Deq [] Empty Nat`, and soundness
  forces `∅ = ω`.

Note the same witness kills **codomain**-injectivity: `P₁` and `P₂`
differ in both positions.  That is what makes the reduction claims'
conclusion existential (above).

**The lesson, which is the transferable part.**  The earlier caution —
"semantic falsity is not evidence about derivability" — was right in
form and useless in substance.  It was unfalsifiable as stated: it
ruled a bad argument out without indicating where a good one would come
from, and so it parked the question indefinitely.  The actual argument
had to come from *inside* the rule set, from `propext`, a rule the
layer has.  **A caution that cannot be discharged either way is not
progress**; when recording one, say what kind of evidence *would*
settle it.  Here that would have been: look for a rule of the layer
that manufactures equations between types with different components —
which is exactly what `propext` does, and it was in `BConst` the whole
time.  A level-guarded variant of injectivity is not
refuted by this, but the layer cannot state the guard and no consumer
needs it.

**Therefore the verdict strengthens** from "needed under the current
rule set" to **needed under every sound rule set**: the only
inversion-based route to the argument's typing at the λ's annotation
runs through domain-injectivity, and no sound extension of this layer
can provide it.  The beta certificate is permanent.

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

### Landed: instantiation commutes (`Setlec/TTVerify/Inst.lean`)

`denote_substFvarAt` and `denote_beta`, transposing
`interp_substFvarAt` and `interp_beta`.  Both predictions from the
analysis held:

* **the cut is free.**  `k = D - p` makes `VExpr.inst`'s *built-in*
  `liftN k` on the substituend be exactly the depth shift, so the one
  interesting case — the variable being substituted for — is
  `denote_lift` and nothing else.  No auxiliary shifting appears in the
  statement, unlike the model's `delV` contraction;
* **every binder case is structural**, because `denote` is.  This is
  the dividend of the `letE` withdrawal above: had `denote` performed a
  substitution, this proof would need lifting-commutes-with-
  instantiation exactly as the shift lemma would have.  It needs
  neither, and between the two lemmas the bridge's entire substitution
  metatheory is `liftN_liftN`, `liftN_zero` and the two closedness
  facts.

### The accounting: four, not 123 — and why it is four

`Setlec/TT/DESIGN.md` §6 makes this accounting for the *layer*:
lean4lean's syntactic metatheory is ~123 substitution lemmas, where the
semantic route needs **two** (`interp_liftN`, `interp_inst`), because
soundness goes straight to the model and no syntactic commutation is
ever needed.

The bridge cannot get to two: it has real de Bruijn bookkeeping, since
`denote` must turn `fvar` levels into indices.  It gets to **four** —
`liftN_liftN`, `liftN_zero`, and the two closedness facts of
`Setlec/TTVerify/VClosed.lean`.

**The number is small for a reason, and the reason matters more than
the number**: `denote` is structural (§2).  A `denote` that performs a
substitution needs lifting to commute with instantiation and with
itself, and four becomes six and then keeps going.  Anyone changing a
`denote` clause to compute something should expect to pay here, and
should check this count before and after.

### Landed: the pieces every clause needs

* `CtxOk.open` (`Setlec/TTVerify/Claims.lean`) — opening a binder
  extends the context correspondence, which every binder clause needs.
* `denote_beta_step` (`Setlec/TTVerify/Inst.lean`) — the beta
  reduction, assembled.  This is §6's argument in mechanized form: the
  premise `HasType Δ x A` has exactly one supplier, the checker's beta
  certificate, and is *not* obtainable from the redex's ambient typing
  (inversion gives the argument at the ambient domain `A₀`, and
  bridging `A₀` to `A` is the open question of §6).

### Next: the remaining `whnfCore` clauses

`whnfCoreBody` (`Setlec/Kernel/Core.lean`) has, beyond the leaf cases
(which are `Deq.refl`) and beta (done):

* **iota** — `iotaRec`, whose set-model counterpart
  `Setlec/Model/Core/Iota.lean` is 1326 lines, plus `NestedFire` and
  `MajorToCtor`.  This is the bulk of the remaining stage-2 work and it
  is where `EnvTT`'s `rec_rules` field gets consumed;
* **projection** — the structural rule plus `projCert` and
  `projLitToCtor`;
* **zeta** — `HasType.zeta`, premise-free, now that `denote` is
  structural at `let`.

Then `whnf` (the delta loop, consuming `defn_eq`), `defeq`, and
`CheckDeclTT` through them.  Scale check against the mirror: the set
model spends ~7500 lines on `Setlec/Model/Core/*` for what
`CheckStepTT` bundles, so this is not one increment.

## 8. Two decisions deliberately left standing

Recorded so they are made rather than inherited.

### DECIDED: the modeled-iota contract is the *fired* form

Made before the install clause rather than during it, and on the
merits rather than by inheritance.  `EnvTT`'s `rec_rules` field will
be **meta-quantified over typed argument terms, concluding `Deq []` at
the applied instance** — not a transposition of the set model's tower
λ-equality (`RecRulesOk`, task #58).

The argument is the general fact of §6, applied.

*Against the tower.*  A closed λ-tower equality has to be **fired** to
be used: apply both sides to the actual arguments (`congrApp`, free)
and then β-reduce each side — and `HasType.beta` demands
`⊢ argᵢ : domainᵢ` **for every argument**.  So the tower form does not
avoid the typing premises; it defers them to the fire site and adds a
β-reduction apparatus on top.

*For the fired form.*  Those same premises are what the install's own
source supplies anyway.  The `_model.iota_j` artefact is a stream
theorem whose denotation is a `pi`-tower ending in `eqE`; instantiating
it at actual arguments is `HasType.app`, which wants exactly
`⊢ argᵢ : domainᵢ`.  Quantifying over them makes them *hypotheses* of
the contract rather than obligations of the install, discharged at the
fire site where the checker's own iota certificates supply them.

*The shape to implement* (recorded so the next increment implements
rather than redesigns).  `iotaRec` fires

```
mkAppN (.const c us) (args ++ [mkAppN (.const cj usj) margs])
  ↦  mkAppN (rl.rhs[us]) (args.take rP ++ margs.drop rl.ctorParams)
```

so `EnvTT.rec_rules` quantifies over `n, cv, mI, rP, rules`, a
non-inert `rl`, its stored constructor, and then over `φ, d, Δ, us,
usj, args, margs`; it takes the two denotations as given (`some L`,
`some R`) plus a **telescope-typing hypothesis** — each argument
denotes and is typed at its domain in the instantiated telescope — and
concludes `Deq Δ L R`.  The telescope-typing predicate is `TeleTyped`
(`Setlec/TTVerify/Tele.lean`): the transpose of `TeleFitI`
(`Setlec/Model/Interp.lean`) with membership replaced by `HasType`, one
premise shorter because `AnnotOk` has nothing to carry.  Its consumer
`TeleTyped.appN` — instantiating a `∀`-telescope typing along a fitting
spine — is proved, which is where the headline fact appears as an
obligation rather than as prose: `HasType.app` fires once per argument
and wants `⊢ x : A` at *that* domain each time, `TeleTyped` supplies
exactly one such premise per argument, and there is nowhere else for
them to come from.  The `iotaCerts` prediction is the claim that the
checker already computes precisely this list.

Note what the fired form costs, stated honestly: the *field* is longer
than the set model's, because the firing conditions move into its
statement.  What it buys is that the *install* only has to denote the
`_model.iota_j` theorem and instantiate it, and the *fire site* has the
premises it needs anyway.  Long statement, short proofs, on both ends.

*And the set model's reason does not transpose*, as suspected.  The
"never resurrect fits-in-clause" ruling was forced by junk-agreement
(two dependent-function graphs agreeing off-domain) and by the `Prop`
collapse.  A syntactic layer has **no off-domain**: a `Deq` at an
instantiation says exactly what it says, and nothing is being compared
away from where it is defined.  The objection is not merely weaker
here — it is inverted, because the "side conditions" it feared are
typing premises, which are this layer's currency.

### `HasType.letE`'s first two premises are not consumed by soundness

`Setlec/TT/Semantics/Soundness.lean`'s `letE` case uses only the third
premise (`ihbody`); the `⊢ ty : sort u` and `⊢ val : ty` premises are
inert there.  That is a quiet violation of the layer's own doctrine —
"rules carry exactly the premises soundness consumes"
(`Setlec/TT/DESIGN.md` §2.4).

They are dischargeable wherever the rule is used, so this is a
doctrinal footnote rather than a bridge obligation, and the bridge
never fires the rule today (stored terms carry no `letE` until task
#117).  Two honest options: trim them, or annotate the rule saying why
they stay — for instance that task #117's `letE` typing will want the
type premise anyway.  Either is fine; leaving it unremarked is not,
because the doctrine is load-bearing elsewhere and an unexplained
exception erodes it.
