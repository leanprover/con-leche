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

## 0. The practice, first — because it produced most of this document

The user's directive for this task was "follow the set model".  Its
operational form is not "copy the proof", and it has turned out to be
the single most productive rule in the work, so it goes first rather
than in a methodology footnote.

> **Before designing a bridge lemma, look for its set-model
> counterpart — not to reuse the proof, but because the counterpart's
> *existence*, *size*, or *absence* usually settles whether the
> statement is right.**

Four instances, none of which were the reason the rule was written
down:

1. **`denote_mono`** replaced the entire `Setlec/Model/Extend/Transport`
   family with one lemma.  The family's *size* was the signal: most of
   it was `AnnotOk` plumbing with no counterpart here.
2. **`certs_typed`** turned out to be `certs_fit`, already proved on
   the other side.  Since `TeleTyped` demands strictly less than
   `TeleFitI`, the counterpart's *existence* settled the `iotaCerts`
   prediction's positive half before a line was written.
3. **The `iotaCerts` pre-registration** got sharp by reading what the
   checker computes, and was then confirmed against `certs_fit`.
4. **The `projCert` branch enumeration** (§6) got its decisive evidence
   from reading the model's own `.proj` case — which showed
   `projCert_inv` feeding a *collapse guard* rather than supplying
   memberships, and led to branch D by exposing that
   `WhnfCoreClaims` takes `AnnotOk` as a hypothesis where
   `WhnfCoreClaimsTT` takes nothing.

**What it guards against.**  Designing a bridge statement that is
subtly wrong in a way only a proof attempt reveals — which, at this
codebase's measured base rate (`Setlec/TT/DESIGN.md` §3.1: three for
three), is the *expected* outcome, not the unlucky one.

**A missing counterpart is informative too**, and is not permission to
proceed: it means either a genuine saving (as with `AnnotOk`) or a
statement that owes its own justification.  Both `cval_closed` and the
`proj` former were found this way — the first as a cost with no
counterpart, the second as a counterpart that could not be
transposed.

**The observable signal, so this is checkable in existing code and not
only in new work.**  When a correspondence is *predicted before* the
definition is written, its consumer applies **without adaptation** —
`eta_rescue` is `m.caps_ok.1` applied to its arguments and nothing
else, and `rec_rules_fire` is two `certs_typed`s and `m.rec_rules`.
When a correspondence is *fitted afterwards*, the consumer needs a
shim: a reassociation, a side lemma, an argument massaged into shape.
So a shim at a use site is a hint that the definition was written to
the wrong shape and adjusted to fit, and is worth re-deriving from the
consumer's needs rather than patching.

### The call-site tell: a fact threaded around an abstraction

> **If several consumers each carry the same fact by hand, the
> abstraction they consume is missing it.**

The most transferable thing this document has produced, and it costs
nothing to check: look at what the *call sites* carry, not only at what
the definition says.

The incident (§8.5): `certs_typed`, `rec_rules_fire` and
`proj_tele_typed` each took `WScoped` and `looseBVarsBounded` in their
own signatures, per argument, and threaded them by hand — because the
claims they consumed did not carry them.  Three consumers doing
identical bookkeeping *around* an abstraction is the abstraction
telling you what it is missing.  The defect was legible in the call
sites long before anyone tried to prove the clause that needed it.

The dual of the practice above it: a **shim** at a use site says the
definition has the wrong *shape*; **repeated bookkeeping** at use sites
says it is missing a *hypothesis*.  Both are read off the consumers,
which is why the consumers are worth reading first.

**The family, closed.**  A third member appeared later (§8.6's
factoring rule) and completes it, because it is the limit case of the
first: a lemma with **no possible consumer**.

| what you see at the use sites | what it says |
|---|---|
| a shim | the definition has the wrong **shape** |
| the same bookkeeping repeated | it is missing a **hypothesis** |
| no use site can exist | it was **sliced where the code does not slice** |

The third is the sharpest because it is not a matter of degree: a lemma
that is true, compiles, and can never be applied is one that cut a
sequential body at a point the body does not expose.  All three are
read off the consumers — including, in the third case, off their
absence.

### The second practice: measure rare shapes; the suite does not cover them

> **A fixture suite being green says nothing about argument shapes it
> never contains.**  Before assuming a shape "never occurs", count it
> in the real stream.

The `Eq` decision (§11) is the instance, and the number is the lesson:
`Eq` is partially applied **once** in ~2000 occurrences in
init-prelude, and **zero** times across all 36 e2e fixtures that
mention it.  A design that special-cased the full spine would have gone
green on the entire suite and failed only on the real input.

*The valuable part is not that the answer was surprising — it is that
the test suite would not have caught it.*  "Fixtures 100 % green, real
stream fails" is the most expensive failure mode this project has,
because it sends you looking at your change rather than at your
coverage.

**And note what made it hard: arity is not greppable.**  The export is
a hash-consed index graph, so answering "is this constant ever applied
to fewer than three arguments" took a walk over the expression table,
not a `grep`.  **A property nobody can check casually is one nobody
will check** — which is an argument for turning it into a *fixture*
rather than a note, so the next person inherits the check instead of
the reasoning.

Open, and worth a sweep: which other constants does the layer treat as
formers, or does reduction special-case by arity?  Each is the same
shape of hole.

**And the failure mode one level up: follow your own asides.**  The
`.proj` resolution (§6) was blocked for a turn by an analysis that
concluded "F1 again" — while the sentence that refuted it was already
in my own notes, filed as an aside: *neither the clause nor `projCert`
checks that `e'`'s inferred type is pair-headed*.  The material was in
hand; the practice was not applied to it.

That is the same class of error this rule exists to prevent, committed
one level up — not "I did not look" but "I looked, wrote it down, and
did not follow it".  So: **an observation you park as an aside is an
unexplored branch, not a footnote.**  Before concluding, re-read your
own asides and ask which of them, followed, would change the
conclusion.  Cheaper written down than relearned.

The rule composes with `Setlec/TT/DESIGN.md` §3.1's house rule
("mechanize a consumer"): §3.1 says do not believe a definition until
something uses it; this says do not *write* the definition until you
have looked at how the other side stated it.

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

> **The claim this section establishes, in the form it should be
> quoted.**  The checker's definitional-equality *unfolding strategy*
> — which constants it unfolds, when, and in what order — is
> irrelevant to the consistency argument, because no unfolding
> decision changes any denotation (`denote_delta_step` is an identity,
> not an equation; §2's "design goal" below).  **That is the whole of
> the claim.**  The rest of `isDefEq` is *not* covered: its β, η, ι and
> projection steps each still owe a `Deq`, and discharging those is
> `DefEqClaimsTT`.  The unbounded version of this sentence would be an
> overstatement that discredits the true part.

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

### The design goal, and how delta realises it

The motivation for this whole line of work was that **the checker's
definitional-equality *unfolding strategy* should be irrelevant to the
consistency argument** — that whether the kernel unfolds eagerly,
lazily, by height, or not at all should not be visible to the proof
that an accepted stream is consistent.  Delta is where that claim is
cashed, so it is worth stating precisely what was reached.

The original sketch predicted a delta step would become `refl` on the
TT side, because the denotation had already unfolded.  **What is
proved is stronger: delta is not a step at all.**
`denote_delta_step` (`Setlec/TTVerify/WhnfCoreStep.lean`) concludes

```
denote cval env φ d e' = some v      -- the same `v`, not a `Deq`-equal one
```

for `e'` the unfolding of `e`.  Not "the two sides are provably equal",
but "there are not two sides": `EnvTT.defn_eq` says a definition's
valuation **is** its value's denotation, so `cval` performed the
unfolding once, at install, and every later unfolding is invisible to
the denotation.  Unfolding is therefore not *justified* by the layer;
it is not *seen* by it.

The difference matters for what the layer can be judged on.  A `refl`
would mean the type theory has a delta rule whose proof happens to be
trivial — and a reader would be entitled to ask what that rule costs,
whether it is confluent with the others, what happens at a
`thmInfo`.  There is no delta rule in `Setlec/TT/Judgment.lean` at all.
Every other reduction clause of the bridge produces a `Deq` because the
layer has a corresponding rule (β, ζ, ι, projection, η); delta produces
none because the layer has no constants to unfold.

That is the same trade as everywhere else in this section — the
denotation absorbs what the layer does not model — and it is why the
payoff arrives with *less* machinery than the sketch assumed: no
unfolding recursion, no well-founded recursion on the environment, and
no termination obligation to discharge.

**The scope of the claim, stated honestly.**  What drops out is the
*unfolding* strategy: which constants the checker chooses to unfold,
when, and in what order, cannot affect the consistency argument,
because no unfolding decision changes any denotation.  What does *not*
drop out is the rest of `isDefEq` — its β/η/ι/projection steps each
still have to produce a `Deq`, and those are the clauses of
`DefEqClaimsTT`.  The claim is about delta, and delta is the part the
reference kernels spend their heuristics on.

### The rest of the transposition

**Every semantic-law field of `EnvModel` now has a transpose.**  What
remains of the correspondence is `ind_ok`'s pair/`PUnit` facts, whose
four λ-tower denotations land with their consumers (§11).

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
| `rec_rules : RecRulesOk` (tower λ-equality) | `rec_rules : RecRulesTT` — **done**, in the *fired* form (§8) |
| `caps_ok : CapsOk` | `caps_ok : CapsOkTT` — **done**, fired form, same argument |
| `proj_ok : ProjOk` | `proj_ok : ProjOkT` — **done**, *verbatim* (the clause is syntactic) |
| `ind_ok`'s pinned-valuation clause | `basis_pinned : BasisPinnedTT` — **done** for the constants the layer carries; the four it derives are fired laws landing with their consumers |
| `nat_ops`, `div_mod`, `reduce_ops` | **done**, all three in the fired form |
| `ind_ok`'s pair/`PUnit` facts | stage 2; the four λ-tower denotations land with their consumers (§11) |

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

### `CheckStepTT`, quarter by quarter (current)

| quarter | status |
| --- | --- |
| `WhnfClaimsTT` | **closed** |
| `InferClaimsTT` | **closed** |
| `WhnfCoreClaimsTT` | closed modulo three chain links (`litMajorToCtor`, `majorToCtor`, `projLitToCtor`) |
| `DefEqClaimsTT` | closed modulo `PairEtaCertStepTT` alone (**blocked on task #130, §13**) |

Discharged inside `DefEqClaimsTT`: `defeqStep_claim`, `defeqLoop_claim`,
`ProofIrrelStepTT`, `DefEqSpineStepTT`, `DefEqStuckStepTT` (all
seventeen clauses of the stuck block), `EtaCertStepTT`,
`StructUnitCertStepTT`, `StructEtaCertStepTT`, and `StuckIrrelStepTT`
modulo `PairEtaCertStepTT`.  The assembly is
`defeq_claimsTT_pairEta`, whose only hypothesis beyond the four
induction hypotheses is that one certificate.

`StructEtaCertStepTT` is worth one line as *confirmation* rather than
as work: it is `eta_rescue` — written for `majorToCtor`'s stuck-major
branch, against the shape `structEtaCertWith` produces — plus a spine
congruence, and the only new lemma it needed was `defEqList_append`
(the certificate splits its argument list at the parameter count and
the fabrication does not).  That the *same* law-consumer serves both
call sites is §6's prediction paying off a second time, and it is also
the sharpest available contrast with §13: `structEtaCertWith` certifies
its telescope, so its bridge lemma is two hundred lines of plumbing
around an existing law; `pairEtaCert` does not, so its bridge lemma
does not exist.

Two definitions changed while closing the stuck block, both §12.10
again and both recorded at their definition:

* **`CtxOk` carries a typing, not an identity** (`Claims.lean`).  The
  model's `FvarsOk` says the variable *inhabits* its annotation; the
  first transposition wrote that as an identity of denotations, which
  no single `Δ` can satisfy for both sides of a binder congruence,
  because the checker opens each body with **its own** annotation and
  the two are only definitionally equal.  Worth noting as a
  *deviation from the reference kernels*: the official kernel's
  `is_def_eq_lambda`/`is_def_eq_pi` push **one** local (the first
  side's domain) for both bodies, ours pushes two.  Aligning the
  checker would have made the identity form work; the bridge fixed
  itself instead, which is the cheaper and more honest direction, but
  the deviation is a finding either way.
* **`BasisPinnedTT` regains the pinned *declaration*** (`EnvTT.lean`),
  dropped as "syntactic, no consumer".  The consumer is
  `ProofIrrelStepTT`'s unit-like branch: `isUnitLikeTy` accepts any
  reserved single-rule zero-field index-free recursor, and identifying
  that family as `PUnit` — the family `HasType.punitEta` is stated at —
  is exactly reading the other four reserved recursors' pinned shapes.

And one claim was under-hypothesised: `DefEqStuckStepTT` needed the two
`reduceNat`-produced-`none` facts, which its call site had and its
statement did not (§8.5 once more).

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

* **Nat literals** (`Setlec/TT/Nat/*`, task #119's other half).

  **LANDED — the correspondence between meta-level `Nat` and the
  layer's `Nat`.**  This was a standing instruction ("prove the
  correspondence") and its cash-out is one lemma, so the decision and
  its realisation are recorded together here rather than left in the
  commit log.  `natLitT_eq_numeral`
  (`Setlec/TTVerify/WhnfCoreStep.lean`):

  > A `Nat` literal's denotation **is** the layer's numeral.

  The two are built identically — `Nat.succ` applied `n` times to
  `Nat.zero` — but over **different constants**, and the reason is
  structural rather than incidental: `natLitT` reads the *valuation*,
  because a denotation cannot know what a stored constant means, while
  `numeral` reads the *basis constants*, because the layer has no
  environment.  `EnvTT.basis_pinned` closes the gap: `Nat`, `Nat.zero`
  and `Nat.succ` are reserved basis names, so a stored declaration
  under one of them is valued by its pin and by nothing else.

  That single lemma is what makes "lemma families, not built-in rules"
  work.  Once a literal *is* a numeral, the meta-induction lemmas below
  apply directly and no 12345-step derivation is ever constructed.  See
  §8.8 for where it sits in the reduction loop.

  The
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

  **LANDED, and stated for an arbitrary domain.**  `Deq.close2` and
  `Deq.close1` (`Setlec/TTVerify/Weaken.lean`) are the recipe
  mechanized:

  > A `Deq` in context `[A, A]` holds at any two terms of `A`, in any
  > context.

  Nothing about `Nat` enters the proof.  That is the evidence the recipe
  was an abstraction rather than a `Nat` trick, and the distinction is
  worth stating precisely because the weaker version sounds the same:
  not "we generalised it and it still worked", but **the general
  statement is what the proof actually proves** — no specialization was
  ever needed to get it through, and none could be removed afterwards.  Step 3
  of the recipe above is also simpler than written — `Deq.intro`
  accepts any proof term, so the two `symm`s the original sketch called
  for are unnecessary; the `eqE` slot being inert does the work
  directly.

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

#### How well confirmed is it, and by what kind of evidence

Three certificates have been checked against it, and **the evidence is
stronger than "three for three" because it is not three of the same
kind**:

* `iotaCerts` — predicted **present**, found present, then *proved*
  (`certs_typed`);
* `structEtaCert` — predicted **present**, found present **verbatim**
  (the predicted call, telescope and arguments);
* `projCert` — predicted to supply the rule's premises, found to supply
  **none of them**, which confirms the fact in the **opposite
  direction**: the rule is unjustifiable exactly where the certificate
  is missing (§10).

**The method discriminates, and that is the load-bearing part.**  The
same reading — take the rule's premises, ask which call establishes
each at the rule's own domain — found the certificate *absent* in one
case and *present word-for-word* in another.  A method that answered
"present" every time would be worthless, and a fact that only ever
predicted presence would be unfalsifiable.  This one predicted an
absence and an implication of that absence (a checker change), which is
why the second column of the verdict table should be read as a finding
rather than as a preference.

*Recording the margin.*  The `structEtaCert` prediction **undershot**:
the eta branch supplies a second `iotaCerts` beyond the one predicted
(task #71's synthetic-spine certification, which types the fabricated
constructor application itself).  Noted as an overshoot rather than
folded into the confirmation — a prediction that undershoots was still
right, and the margin tells the next reader how tight the reasoning
was.  It was not tight: the branch has more than the contract needs.

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

**Note that the third column does not read "no" everywhere**, and that
is the point: the last two rows come out differently.  A pattern that
made every certificate permanent would be suspiciously convenient and
worth less — a theory that explains every row explains none of them.
The split below is what makes the five "no"s worth reading rather than
motivated.

| certificate | checker can skip | bridge can do without | status |
|---|---|---|---|
| app-argument re-check (`inferSpineI`) | yes — the 98.6 % | **no** | *established* (four routes closed) |
| beta re-check | yes | **no** | *established* (`propext` refutes the alternative) |
| iota telescope certifications (`iotaCerts`) | yes | **no** | **prediction** |
| structure-eta / unit-like telescope certifications | yes | **no** | **confirmed, verbatim** (below) |
| `projCert` | yes — measured free anyway | **no** — and it supplies *none* of the rule's premises | **resolved: branch A** (below) |
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

#### The `iotaCerts` prediction: tested early, and it holds — now mechanized

Tested first by *reading*, before the field statement was written — the
asymmetry favoured it, since a failure would have invalidated a
contract shape built on top of it.  The reading has since been
**discharged as a proof**: `certs_typed`
(`Setlec/TTVerify/Certs.lean`) is the transpose of `certs_fit`, and it
builds a `TeleTyped` from a successful `iotaCerts` run.

`iotaCerts` (`Setlec/Kernel/Core.lean`) walks a telescope one argument
at a time, instantiating `body.instantiate1 arg` as it goes, and per
argument produces exactly `infer arg = .ok ta` and
`defeq ta ty = .ok true`.  Through `InferClaimsTT`, `DefEqClaimsTT` and
`Deq.conv` that is `HasType Δ ⟦arg⟧ ⟦ty⟧` — precisely
`TeleTyped.cons`'s typing premise, at precisely its domain.  **Same
walk, same order, same arrangement: exact, not a superset and not
adjacent.**

The decisive corroboration is that **the set model already has this
lemma**: `certs_fit` (`Setlec/Model/Core/Certs.lean`) builds `TeleFitI`
from `iotaCertsP` by exactly this induction, via `iotaCerts_step_inv`.
`TeleTyped` is `TeleFitI` with membership replaced by typing and **one
premise fewer** (`AnnotOk` dropped), so it demands strictly less than
what `iotaCerts` is already known to supply.

*What this does and does not establish.*  The **positive** half is now
proved, not merely checked: the checker computes exactly the facts the
contract needs, one `HasType Δ ⟦arg⟧ ⟦dom⟧` per argument at the domain
the rule fires at.  The
**negative** half — that nothing else could supply them — still rests
on the headline fact's argument, not on a mechanized proof, and the
falsification test as set ("a clause discharges its rule's premises
without the certificate") is only run when the clause is proved.  The
other two rows are untested.

*For the next increment*: `iotaCertsP` and `iotaCerts_step_inv` both
live in `Setlec/Verify/*`, so they are importable from here.  The
transposed `certs_typed` needs no re-derivation of the inversion — only
the two substitutions (membership → typing, `AnnotOk` → nothing).

#### PRE-REGISTERED: what `structEtaCert` and `projCert` are expected to discharge

Written **before** the `majorToCtor` and `.proj` clauses, because a
prediction recorded afterwards is not a prediction.  Naming the rule,
the premise and the domain in each case, so the check is a comparison
and not a vibe — the form that paid twice for `iotaCerts`.

**`structEtaCert` — CONFIRMED, verbatim, on both counts.**  The
pre-registration is reproduced unchanged below; the result follows it.  At the ι-time eta rescue the bridge must
produce `Deq Δ ⟦b⟧ ⟦C p⃗ (proj₀ p⃗ b) … ⟧`, which will come from the
`EtaLaw` transpose in `caps_ok`.  In the fired form (matching §8's iota
decision) that law is hypothesised on exactly two things, and I expect
`structEtaCert` to supply both:

* `TeleTyped` for `T`'s parameter telescope at `p⃗ = wtb.getAppArgs` —
  from `structEtaCertWith`'s own `iotaCerts` call on
  `cvT.type.instantiateLevelParams …`, i.e. the same fact `certs_typed`
  already extracts, at `T`'s parameter domains;
* `HasType Δ ⟦b⟧ ⟦T p⃗⟧` — from `structEtaCert`'s `infer b` plus the
  whnf claim on its type, at the domain `T p⃗`.

*Result.*  `majorToCtor`'s eta branch computes
`tmaj ← r.whnf depth (← r.infer depth major)` and calls
`structEtaCertWith … fab major tmaj`, whose body runs

```
iotaCerts r env depth
  (cvT.type.instantiateLevelParams cvT.levelParams us') wtb.getAppArgs
```

— **the predicted call, at the predicted telescope, on the predicted
arguments**, with `wtb = tmaj`.  And the subject's typing comes from
the `infer major` that produced `tmaj`, at the domain `T p⃗`, as
predicted.  The branch supplies *more* than was predicted: a second
`iotaCerts` (task #71's synthetic-spine certification) certifies the
fabricated constructor spine against the **constructor's** telescope,
which is what types `fab` itself.

*Why this result matters beyond the row.*  The same reading method,
applied to `projCert`, found the certificate **absent** (branch A);
applied here it finds it **present and verbatim**.  A method that
returned "present" both times would be worthless.  This one
discriminates, which is the evidence that the second column of the
table is a finding rather than a preference.

**`projCert` — expected to confirm only *partly*, and this is the row I
expect to fail if any does.**  `projCert` checks **sorts**, not
argument typings: the field's type whnfs to `.sort uT` with
`uT ≡ fieldLvl`, and the subject's type to `.sort wT` with
`wT ≡ structLvl`.  So:

* I expect it to discharge the **sorting** premises of
  `projFstMk`/`projSndMk` — `⊢ A : .sort u` and
  `⊢ B : arrow A (.sort v)` — at the levels the entry pins.
* I **do not** see where the two *argument-typing* premises
  (`⊢ a : A` and `⊢ b : .app B a`) would come from.  `whnfCoreBody`'s
  `.proj` clause calls no `iotaCerts`, and by the headline fact the
  ambient typing of the subject yields them only at *some* domain, not
  at the pinned one.

So the pre-registered outcome for `projCert` is a **split**: sorting
premises yes, argument-typing premises from somewhere else.  *Where*
else has three possible answers, enumerated here before the proof so
that whichever holds, the record shows it was considered.

**Branch A — a gap in the checker.**  The `.proj` clause certifies less
than its rule needs, and the missing certificate is real.

**Branch B — §6's fact is wrong here.**  The premises turn out to be
recoverable from ambient facts after all, in which case the headline
fact fails in the `.proj` case, which is the larger result.

**Branch C — the premises come from the subject's own derivation,
and no certificate is needed by either side.**  The evidence: the set
model proves this clause today, and **not from `projCert`** — its
`projCert_inv` feeds the *collapse guard* (`Nat.max … = 0` ⇒ everything
is the proof point), i.e. level facts, exactly as predicted for the
sorting premises.  Its membership facts come from `AnnotOk`'s own
`.proj` clause, which post-#100 *inference* establishes.

*One concrete mechanism for C was proposed and has been **checked and
refuted***: that `whnfCoreBody`'s `.proj` clause must infer the subject
in order to find the structure entry, which would hand the bridge
`HasType Δ ⟦p⟧ ⟦tp⟧` for free.  **It does not infer the subject.**  It
reads the structure name off the *node* — `env.findProj? sn i` where
`sn` comes from `.proj sn i pe` — and matches `e'.getAppFn` against
`entry.ctor`.  No inference of the subject happens in the clause
itself.

A weaker version does hold and should be weighed: **`projCert` infers
both** the field (`ta`) and the subject (`te`), and merely compares
their *sorts* to the entry's pinned levels.  So `InferClaimsTT` does
yield `HasType Δ ⟦arg⟧ ⟦ta⟧` and `HasType Δ ⟦e₂⟧ ⟦te⟧` — but at the
*inferred* types, and reaching the entry's *pinned* domains from there
is §6's question again, which says it does not go through.

**D — a finding about my own claim shape, and the reading above makes
it likeliest.**  The check located *where* the missing fact lives:
`whnfCoreBody`'s `.proj` clause relies on an invariant established by
the **annotate** pass, whose own `.proj` clause *does* infer the
subject, whnf its type and normalise the node's `sn` to that head.  The
set model carries exactly that invariant into reduction —
`WhnfCoreClaims` takes `AnnotOk … e` as a **hypothesis**, and its
`.proj` conjunct is the `sigmaSet` membership.  `WhnfCoreClaimsTT`
carries nothing.

#### RESOLVED: branch A, and the missing fact is a certificate the clause does not run

**RETRACTION.**  The previous revision of this subsection concluded
that D's fact is *semantic* and that the obstruction is F1 at a third
site: "the clause reduces `e' = whnf p` and needs premises about `e'`'s
components, and moving a typing from `p` to `e'` across `Deq` is
exactly the schema F1 refutes".  **That is wrong.**  It assumed the
only source of a typing for `e'` is transport from `p`.  It is not:

> **`projCert` infers `e'` itself** —
> `projCert r env depth e' i …` at the call site, and inside,
> `let te ← r.infer depth e₂` with `e₂ = e'`.

So `InferClaimsTT` yields `HasType Δ ⟦e'⟧ ⟦te⟧` *directly*, about the
reduct.  No transport, no `Deq`, **F1 never enters**.  The error was
not following an observation I had already made and filed as an aside
("neither the clause nor `projCert` checks that `e'`'s inferred type is
pair-headed") to its conclusion.

**And a correction to the pre-registration, against my own favour.**
It predicted `projCert` would discharge `projFstMk`'s *sorting*
premises.  On a closer read it discharges **none of the four**:
`projCert` checks the sort of the **field's type** and of the
**subject's type**, never the sorts of the *parameters* `A` and `B`;
and its `⊢ ⟦arg⟧ : ⟦ta⟧` is the field at its *inferred* type, not at
`A` or at `.app B a`.

*What is actually missing.*  For the pinned pair, `projFstMk`/
`projSndMk` want, with `⟦e'⟧ = psigmaMkT u v A B a b`:

```
⊢ A : .sort u      ⊢ B : arrow A (.sort v)      ⊢ a : A      ⊢ b : .app B a
```

which are **exactly the four telescope domains of `PSigma'.mk`'s stored
type** — so exactly what an `iotaCerts` on the constructor spine would
produce, and what `certs_typed` converts to `TeleTyped` (modulo the
pinned-basis valuation clause fixing `⟦e'⟧`'s shape).  `iotaRec`
already makes precisely this call for its constructor telescope; the
`.proj` clause does not.

So **branch A holds**, in the careful sense and not the alarming one:

> The checker **certifies less than its rule needs**, so the bridge
> cannot reconstruct a derivation.  It is **not unsound** — nothing
> here says the reduction is wrong, only that the checker does not
> write down enough for a derivation to be rebuilt from it.

**§6 is confirmed, not dented.**  The repair supplies the premise
exactly where the rule fires, as an argument-typing-at-a-domain
certificate — the kind the two-column table already predicts is
permanent for the bridge.  Branch C is refuted (the derivation does not
supply it); branch B is refuted (§6 stands); branch D is withdrawn (no
claim-shape revision is needed, and no `AnnotOk` analogue).

**This is the first case where the bridge tells us to change the
checker** rather than the reverse — the bridge earning its keep as a
design instrument, not only as a verification.

*Not implemented here.*  A kernel change needs its own task, gates and
byte-identity story, and must not ride along inside a proof branch.
The `.proj` clause of `Setlec/TTVerify/WhnfCore.lean` stays unproved
until it lands.

Note carefully what D is **not**: it is not the threading withdrawn in
`Setlec/TTVerify/Claims.lean`.  That withdrawal was about the
*conclusion* being unattainable (a reduct's typing at the subject's
type).  A hypothesis without a conclusion is a different object, and
whether it is usable turns on whether each clause's re-entry can obtain
typing from its own certificates.  The two must not be collapsed.

**If C holds, the branch-A framing must not survive into this
document**: a reader who finds "gap in the checker" recorded here will
go looking for a bug that is not there.

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

### The substitution algebra: available, and deliberately not the default

`Setlec/TTVerify/{SubstAlgebra,HasTypeSubst}.lean` (landed separately)
supply `HasType.weakenHead` (head extension *with* lifting —
complementary to `Weaken.lean`'s lift-free `weakenTail`, not a
duplicate), `HasType.instantiate`, and a `liftN`/`inst` commutation kit
over the smart constructors.  19 substantive lemmas.

**They are the fallback for the residue, not the default**, and the
policy is worth restating here because it is easy to erode: the
*object-level* route — `lam`, then `app` at the closed arguments so the
rule's own `B.inst a` does the instantiation **in the type**, then two
`symm`s for the inert `prf` subject (§5) — is preferred wherever it
works.  Two increments have avoided needing the algebra by taking it
(the `Nat` recipe; the `Deq`-at-numerals move), and a hammer reached
for first would undo that.  *Using `instantiate` where the object-level
route would have worked is worth noticing rather than shipping.*

**A finding from that work, which corrects an estimate I would
otherwise have repeated**: rules embedding inner lifts (`natStepT`,
`quotInvT`, `arrow`, `relT`, `eta`, `funext`) force the full
commutation kit **already for weakening** — weakening-with-lifting is
not the cheap half it looks like.  So do not price "just weakening" as
a small ask; that was exactly the miscalculation available at §10.2,
where the workaround's cost was the argument for the rule change.

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

(The 19 lemmas of the substitution algebra are *not* a refutation of
this count: they exist for `HasType`-level weakening and substitution,
which the structural `denote` never needed, and they are a fallback the
clauses have so far not used.  The count to watch is still the one
above — if a `denote` clause starts computing, it rises.)

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

### The iota clause, decomposed

Scouted before starting it, per §0 — and the scouting changed the
estimate.

`iotaRec_inv` (`Setlec/Verify/InferLemmas.lean`) is **importable** and
inverts the whole guard cascade in one step, handing over: the stored
recursor and constructor, the rule, the level and argument spines,
*both* `iotaCertsP … = .ok true` facts, and `eout` in exactly the form
`RecRulesTT` concludes about.  So the clause splits cleanly:

1. **Assembly — done** (`rec_rules_fire`,
   `Setlec/TTVerify/Iota.lean`).  `certs_typed` twice, once per
   telescope, then `EnvTT.rec_rules`.  It compiled on the first
   attempt, which is what "de-risked by scouting" was supposed to buy
   and did.  The scoping side conditions are hypotheses, to be
   discharged by the clause from `EnvTT.wf` and the reduction's
   invariants, exactly as the set model's iota case discharges its
   own.
2. **`majorToCtor` soundness** — its prediction settled
   (`structEtaCert` confirmed, §6), and its **eta branch done**
   (`eta_rescue`, `Setlec/TTVerify/Iota.lean`), which is the branch the
   prediction was about.  The **K branch** is *blocked*, not merely
   pending: its certificate identifies inhabitants of two *different*
   `Prop`s (and, in the unit-like branch, of `PUnit` at two different
   levels), while the layer's `proofIrrel`/`punitEta` demand one type
   for both.  Both rules are over-constrained relative to their own
   soundness proofs; see §10.2.  The contract
   speaks about a redex whose major is already in constructor form,
   while the clause sees the major as written.  Bridging them is the
   whnf claim on the major, `litMajorToCtor`, and `majorToCtor` — the
   last being the ι-time structure-eta *rescue*, whose set-model
   counterpart (`Setlec/Model/Core/MajorToCtor.lean`) is 550 lines.

**Both predictions it carried have now been tested by reading**, before
the proof: `structEtaCert` **confirmed verbatim**, `projCert`
**resolved as branch A** (the certificate is absent and the checker
needs one, §10).  So the remaining work in item 2 is proof, not
discovery: the eta branch's facts are known to be there, and the K
branch's `proofIrrel` route is the pinned-`PUnit`/`Prop` case where
both sides collapse.

Three for three on §6's fact, counting `iotaCerts`, `structEtaCert`,
and `projCert` — the last confirming it in the *opposite* direction,
by the rule being unjustifiable exactly where the certificate is
missing.

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
merits rather than by inheritance.  `EnvTT`'s `rec_rules` field is
**meta-quantified over typed argument terms, concluding `Deq` at
the applied instance** (`RecRulesTT`, landed) — not a transposition of the set model's tower
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

*The shape, as landed.*  `iotaRec` fires

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

#### The decision, closed: five fields, one shape

The fired form was argued for once, at `rec_rules`.  It is now the
shape of **every** semantic-law field: `rec_rules`, `caps_ok`,
`nat_ops`, `div_mod`, `reduce_ops`.  Each quantifies over the syntax
the checker matched on, takes the denotations as given, adds typing
hypotheses at the rule's own domains, and concludes a `Deq`.

That is worth stating because of what it changes for a reader:
*"we chose the fired form"* has to be taken on trust, while **"five
fields, one shape"** can be checked by looking.  A uniform structure is
also a thing to notice being broken — if a sixth field arrives in a
different shape, either it has a reason or it is a mistake, and both
are easier to see against four precedents than against one.

*And the set model's reason does not transpose*, as suspected.  The
"never resurrect fits-in-clause" ruling was forced by junk-agreement
(two dependent-function graphs agreeing off-domain) and by the `Prop`
collapse.  A syntactic layer has **no off-domain**: a `Deq` at an
instantiation says exactly what it says, and nothing is being compared
away from where it is defined.  The objection is not merely weaker
here — it is inverted, because the "side conditions" it feared are
typing premises, which are this layer's currency.

### 8.1 Correction: the fired form must not quantify over `Expr`s

**The decision above survives; the shape it was recorded in does not.**
Found while building the first field transport (`rec_rules` across a
fresh install), and worth recording as a *correction* rather than a
tidy-up, because the fired form was written down as closed.

As first stated, `RecRulesTT` quantified over the argument
*expressions* `args margs : List Expr` and took the redex's and
reduct's denotations as **hypotheses**.  That does not transport.  An
install grows the environment, so a law about `⟨c₀ :: env⟩` has to be
discharged from the law about `env`; but the arguments quantified over
in the bigger environment may mention `c₀`, and then they have **no
denotation in the smaller one**.  `denote_mono` runs the wrong way, and
no side condition repairs it: the arguments are arbitrary, and at a
fire site inside `checkDecl` they really can mention the constant just
installed.

The general rule the episode establishes, which applies to any
environment-indexed invariant and not just to this one:

> **Every environment-dependent fact in a law's *hypotheses* must be
> about a *stored* expression.**  Facts about arbitrary expressions may
> appear only in the conclusion.

**The mechanism is variance**, and the rule should always be quoted with
it, because the reason is what tells you when it generalises.
Hypotheses are contravariant: to prove a law in the larger environment
you must *use* the law from the smaller one, so every hypothesis of the
larger law has to be dischargeable in the smaller.  A fact about a
**stored** expression transports downward, because the expression is
still stored there and `constsResolve` says so.  A fact about an
**arbitrary** expression does not, because the expression may mention
the constant that was just installed.  Conclusions run the other way
and are free.

**The statement-level tell** — check it without doing any proof: *a
hypothesis that mentions both the environment and a universally
quantified expression*.  That combination is precisely the
contravariant one, and it is visible in the definition.

The set model obeys this without ever saying so, and that is why
`EnvModel` transports: `EtaLaw` quantifies over `ps : List V` — values,
not expressions — and its one `Expr` is `cvT.type`, which is stored.
Its transport (`CapsOk.cons`, `Setlec/Model/Extend/Sibs.lean`) then runs
that single hypothesis *down* through `TeleFit.env_shrink`, guarded by
`Expr.constsResolve`, which `EnvWF` supplies for stored types.  Reading
that proof is what identified the fix; **the shape was in the model all
along, and the fired form's mistake was to depart from it in a detail
that looked cosmetic.**

The repair, taken:

* the spines move to `VExpr` (`VTeleTyped`, the transpose of `TeleFit`,
  beside the existing `TeleTyped`, which is `TeleFitI`'s transpose —
  the model keeps both for the same reason);
* the remaining `denote` hypotheses are all of stored expressions, and
  transport by `denote_env_shrink`, the transpose of `interp_mono`;
* the `constsResolve` side conditions the transports need are *not*
  added as field clauses: `EnvTT` already carries `wf : EnvWF env`,
  which supplies every one of them.  Clauses were briefly added
  mirroring `RecRulesOk`, then removed — see the "too strong" note
  below.

The cost lands where the model pays it too: at the *consumer*.
`rec_rules_fire` now has to split the recursor's certified spine at its
major premise and rebuild both sides as `VExpr` applications
(`DenoteSpine.snoc_inv`, `.append`, `.take`, `.drop`, `.map`).  That
bookkeeping is not incidental — it is the price of a law whose
quantifiers do not mention the environment, and it is the right price.

**A correction to §8's own framing, from the coordinator, recorded
because the flawed version is quotable and should not survive.**  When
the contract decision was closed, "five fields, one shape" was endorsed
as the *checkable* claim, against "we chose the fired form" as the one
requiring trust.  That was too generous.  Uniformity is checkable, but
it establishes **consistency, not correctness** — and here all five
fields shared one defect, so the uniformity being praised was uniform
wrongness.  The defensible reading: a uniform structure makes a
*deviation* easy to spot, which is worth having, but it is no evidence
that the shape is right.  Read §8's closing paragraphs with that
caveat.

**What actually confirmed the diagnosis** was not uniformity but its
opposite: `ReduceOpsTT` and `DivModTT` needed no change at all, having
been `VExpr`-only from the start.  Two fields that were already right,
for reasons unconnected to the repair, agreeing with the repair's
prediction — that is evidence; five fields agreeing with each other is
not.

**And on §0's practice.**  This is the "look for the set-model
counterpart" habit catching an error *already made* rather than
preventing one.  Both are wins; only the second is comfortable, and a
practice that only ever caught errors in advance would be one nobody
had tested.

### 8.6 The `whnfCore` step, and obligation granularity

The first quarter of `CheckStepTT` is proved
(`Setlec/TTVerify/WhnfCoreStep.lean`), modulo two named obligations.
Seven of nine clauses are complete: the six leaves, `bvar` (outside the
fragment — and note the bridge refutes it from the *denotation*,
`.bvar` denoting to `none`, where the model refutes it from the
checker's `throw`), zeta, and the whole application clause including
its β sub-case.

**The β clause is §6's headline fact at its most visible.**
`whnf_app_inv` hands back the two certificate runs; the inference claim
turns one into `⊢ ⟦a⟧ : ⟦ta⟧`, the equality claim turns the other into
`⟦ta⟧ ≡ ⟦ty⟧`, and `Deq.conv` combines them into the argument typed at
**the domain the redex names** — exactly `HasType.beta`'s single
premise. Nothing carried from above would supply it.

**The two obligations are stated at different granularities, on
purpose.**  `IotaStepTT` is at *reduct* granularity: `whnf_app_inv`
hands the ι case its reduct directly, so the obligation isolates to
"this reduct denotes `Deq`-equally and is well-scoped" and the rest of
the application clause is proved around it.  `ProjStepTT` is at
*clause* granularity, because the projection clause reduces its
scrutinee with `whnf` and expands string literals with
`projLitToCtor` before the table is consulted — isolating its reduct
would leave two unproved steps *outside* the obligation instead of one
*inside* it.

The rule that produced that choice, worth keeping: **put the boundary
where it leaves the fewest unproved steps outside it.** An obligation
is a promise about what remains; a promise that leaves debris around it
is worse than a larger promise that does not.

**The three rules, and what each answers.**  They arrived separately
and are a set: §8.6's *boundary* rule says **where** to put an
obligation (fewest unproved steps outside it); §12.7's *estimation*
rule says **how big** it is (read the inversion, not the conclusion);
and the rule below says **where factoring is possible at all**.  Apply
them in that order — the third can veto the first.

**Where a checker body may be factored at all** (learned by producing a
non-composable lemma and withdrawing it within the hour):

> **A checker body factors into lemmas exactly where the *checker*
> factors into functions.**

`whnfLoop`/`whnfStep` and `defeqLoop`/`defeqStep` factor, so the loop
lemmas do — one budget induction each, with the continuation
abstracted, because the checker abstracted it first.  The moves
*inside* `defeqStep` do not factor: they are sequential, each
consuming the residual hypothesis the previous `split` left, and that
residual is a tail of an anonymous `do` block with nothing to name it
with.  A lemma ending after two moves can return the facts it derived
but not the residual, so the next move cannot start where it stopped.

The practical consequence: `defeqStep`'s claim is one proof.  Trying to
slice it finer produces lemmas that are true, compile, and have no
possible consumer — the "shim at a use site" tell (§0) reaching its
limit case, where there is no use site at all.

**But there is a second kind of slice, and it is legitimate**:

> **You may not slice a body into stages; you may slice its input
> space into cases.**

Every clause lemma in this bridge is the latter — `infer_app_claim` is
`inferBody` restricted to `.app`, and it composes because its
hypothesis is `inferBody`'s *own* call.  `DefEqStuckStepTT` is the same
move at `defeqStep`: its hypothesis is `defeqStep`'s own call with the
earlier moves' *negative outcomes* recorded as hypotheses, so a
consumer applies it to the untouched original.  A stage lemma cannot
return its position; a case lemma never left the entry point.

The tell that distinguishes them, at statement time: **does the
hypothesis name the function, or a point inside it?**  `DefEqLeafStepTT`
had to invent a dummy continuation to phrase itself, which is that
question answering itself.

And the constructive half: **the stuck block did not need a fabricated
boundary, it needed its cases named by what failed before them.**  Once
`DefEqStuckStepTT` records the earlier moves' *negative outcomes* as
hypotheses, it is a case restriction on `defeqStep`'s own call and
composes.  Every stage split this bridge wanted has had such a
reformulation available; none has needed a boundary the checker does
not draw.

**What these rules are for**, stated because the episode says it
better than a claim could: writing the factoring rule down did not stop
me drafting a violation of it — reading it back did, twenty minutes
later.  **They do not prevent errors; they make them cheap to catch at
statement time instead of expensive to discover at composition time.**
That is the whole return, and it is why the tells are all phrased as
things visible in a *statement* rather than in a proof.

**The same question from the estimation side** (learned the hard way in
§12.7, and recorded here because it belongs with the boundary rule):
**estimate an obligation from the checker function it inverts, not from
the shape of its conclusion.**  A statement naming two terms can hide a
four-step chain between them — `IotaStepTT` names a redex and a reduct
and `iotaRec_inv` puts `whnf`, `litMajorToCtor` and `majorToCtor`
between them.  Reading the statement gives the wrong number; reading
the inversion gives the right one.

The two halves compose: estimate from the inversion, then place the
boundary so the debris is minimal.  Applying both to `IotaStepTT`
splits `MajorToCtorStepTT` out of it — which is the boundary rule
applied to its own earlier output.

**What the two obligations still need is frame conditions, not
equations.**  Their equational content exists (`rec_rules_fire`,
`proj_reduction_step`, `proj_tele_typed`).  What is missing is that the
reduct must be handed to the recursive `whnfCore` call already
well-scoped, and the checker side supplies only one of the four facts
needed: `iotaRec_WScoped` (`Setlec/Verify/Deep.lean`, made public for
this — it was `private` only as that file's blanket style for local
helpers).  There is no `iotaRec_looseBVars` and no
`iotaRec_fvarLeaves` at all.

That is not an oversight in `Setlec/Verify/*`: the set model does not
use standalone lemmas either.  Its `iota_sound`
(`Setlec/Model/Core/Iota.lean`) *returns* all four frame conditions
alongside the equation, as part of one conclusion.

**`IotaStepTT` was given that shape before the correspondence was
noticed**, and that is the point worth recording rather than the
visibility change that led to it.  The obligation was sized by asking
what the recursive `whnfCore` call needs; the model was sized by the
same question years earlier; the two arrived at the same
all-four-in-one-conclusion shape independently.  **Independent arrival
at the same shape is the best evidence available that an obligation is
right-sized** — better than either derivation alone, because neither
was fitted to the other.  So the bridge's obligation is not oversized:
it is the same size as the model's, and the model spends 1326 lines on
it.

One incidental catch: `denote_beta_step_certified` first carried an
unused `{mb : BinderMeta}` implicit, copied from the λ's binder.  Lean
refused to synthesize it — an unused implicit that appears in no
hypothesis cannot be inferred — which is the one variety of §8.2's
defect the elaborator catches for you.

### 8.7 The delta step is an identity, not an equation

`whnfStep`'s third move — unfold one stored definition — turned out to
be the cheapest clause in the bridge, and for a reason worth recording
because it will not recur: **the reduct denotes to the *same* term, not
merely to a `Deq`-equal one.**  `EnvTT.defn_eq` says a definition's
valuation *is* its value's denotation, so unfolding is invisible to the
denotation and the clause's equation is `rfl`.

Every other reduction clause produces a `Deq` because the layer's rule
does (β, ζ, ι, projection).  Delta produces none because there is no
delta *rule* in the layer at all — the layer has no constants to
unfold; the bridge's `cval` has already done the unfolding, once, at
install.  That is the same trade as everywhere else in §2: the
denotation absorbs what the layer does not model.

Two pieces it needed, both now landed and both wanted elsewhere:

* `denote_instLevels` — level instantiation composes the assignment,
  the transpose of `interp_instLevels`.  `unfoldDefinition`
  substitutes levels *into* the stored value while `defn_eq` speaks
  about the value under a substituted *assignment*; this is the bridge
  between the two.  Its literal clauses cost nothing, because §8.4's
  guards carry them.
* `denote_mkAppN_inv` — the converse of `denote_mkAppN`, to read a
  redex apart.  The forward direction had existed since the eta
  rescue; the converse is what a *reduction* clause needs, and every
  remaining spine clause will want it.

Note what did *not* need adding: the "closed values are
depth-independent" step is `denote_lift` at `p = 0` composed with
`cval_closed`, both already present.  The model needs a dedicated
`interp_closed_invariant` for the same step because its valuation
carries the depth; the bridge's lift is enough.

### 8.8 The reduction loop, and where the strategy-independence shows

`WhnfClaimsTT` at `fuel + 1` is closed
(`Setlec/TTVerify/WhnfCoreStep.lean`), modulo one named obligation.
It is the shortest of the four quarters, because `whnfBody` *is*
`whnfLoop` and the loop's budget induction is structural: three moves
per iteration, and nothing from the `Nat` machinery is needed to
sequence them.

**Which moves contribute an equation, and which does not.** The
`whnfCore` move contributes a `Deq` (β, ζ, ι and projection all have
layer rules). The literal move contributes a `Deq` (the recurrences
are `Deq`s). The delta move contributes **nothing** — it is an
identity (§2). So the equation the loop accumulates is exactly as long
as the number of *non-delta* steps, however many constants were
unfolded on the way. §2's claim that the unfolding strategy drops out
of the consistency argument is visible right there in the proof term:
`hD₁.trans hD₃` in the delta branch, where a `refl`-based treatment
would have had three `trans`es and a strategy-dependent chain length.

**The literal bridge is the piece that made `reduceNat` tractable at
all**, and it is §5's recipe in one lemma: `natLitT_eq_numeral` says
the bridge's `natLitT` and the layer's `TT.numeral` are the same term.
They are built the same way — `Nat.succ` applied `n` times to
`Nat.zero` — but over different constants: `natLitT` reads the
*valuation*, because a denotation cannot know what a stored constant
means, while `numeral` reads the *basis constants*, because the layer
has no environment.  `EnvTT.basis_pinned` closes the gap: `Nat`,
`Nat.zero` and `Nat.succ` are reserved basis names, so a stored
declaration under one of them is valued by its pin and by nothing else.

That is the whole of why "no 12345-step derivation" works.  Once a
literal *is* a numeral, `Setlec/TT/Nat/*`'s meta-induction lemmas apply
directly, and the remaining obligation (`ReduceNatStepTT`) is only the
closing of `nat_ops`' open equations at numerals — the `lam`-twice,
`app`-twice recipe already written down at `NatOpsTT`.

Three of the four quarters' *structure* is now settled; what is
outstanding is three named obligations (`IotaStepTT`, `ProjStepTT`,
`ReduceNatStepTT`) and two whole quarters (`DefEqClaimsTT`,
`InferClaimsTT`).

### 8.9 The `Nat` fast path, end to end at one operation

`Setlec/TTVerify/NatOpsStep.lean` closes the chain for `Nat.add`, and
the point of doing one operation in full before the other six is that
the chain is what needed validating, not the arithmetic:

```
EnvTT.nat_ops                    -- the stored recurrences, open at [Nat, Nat]
  → Deq.close2                   -- §5's recipe: closed at two numerals
  → numeral_add                  -- the layer's meta-induction
  = Deq Γ (add ⌜a⌝ ⌜b⌝) ⌜a + b⌝
```

`natOps_add_closed` is three lines and **no derivation proportional to
the literals is constructed anywhere**: `numeral_add`'s recursion is at
the *meta* level, over Lean's own `Nat`, and the `Deq` it produces has
`prf` as its proof term whatever the literals were.  That was the
requirement the whole "lemma families, not built-in rules" design was
chosen to meet, and this is where it is checkable.

**What each remaining operation costs.**  Only *shape* work: read the
denotation of that operation's equation sides into the form its
meta-induction lemma states its hypotheses at.  The pieces are all
shared —

* `denote_natOp_x` / `denote_natOp_y` — the two free variables at
  indices 1 and 0;
* `denote_const_nolevels`, `denote_natZeroT`, `denote_natSuccT` — the
  three primitives, each discharging its side condition from the guard
  (§8.4 again);
* `cval_natT`, `numeral_closed` — what `Deq.close2` needs to fire.

— so a clause is a `rw` chain and a `simpa`, and nothing in
`natOps_add`'s argument is `add`-specific.  The six structural
siblings differ only in which primitives appear on the right; the nine
WF operations go through `EnvTT.div_mod` and
`Setlec/TT/Nat/WfOps.lean` instead, with the same shape.

One thing worth noting for whoever writes the rest: the equation sides
are extracted with `by decide` on `(natOpEquations 0 c)[i]!`, which
works because the equation list is a closed computation.  That is
cheaper than destructuring `natOpEquations`' `if`-chain, and it keeps
each clause independent of the others' positions.

### 8.5 The claims were *under*-hypothesised — the dual of §8.2

Found on the first clause of `CheckStepTT`, before writing any proof:
the `whnfCore` zeta clause needs `fvarsBelow d b`, `WScoped d v` and
`v.looseBVarsBounded 0` to apply `denote_beta`, and
`WhnfCoreClaimsTT` supplied none of them.

The set model's claims carry **three** syntactic frame conditions —
`WScoped d e`, `e.looseBVarsBounded 0 = true`, `Expr.LeavesBounded e` —
alongside the two semantic ones (`FvarsOk`, `AnnotOk`).  When the
claims were transposed, `AnnotOk` was dropped for the right reason (it
has no counterpart) and `FvarsOk` was absorbed into `CtxOk` for the
right reason (the context replaces the valuation) — but the three
syntactic conditions were dropped *along with them*, which was wrong:
they are facts about `Expr`, they transpose verbatim, and both sides
need them for the same reason.

**The tell was already in the source.** `certs_typed`, `rec_rules_fire`
and `proj_tele_typed` each carried `WScoped`/`looseBVarsBounded`
explicitly, per argument, in their own signatures — because the claims
they consumed did not.  A fact being threaded by hand *around* an
abstraction is evidence the abstraction is missing it.  That is the
under-strong counterpart of §8.2's tells, and it has the same remedy:
read what the proof actually needs, not what the statement happens to
offer.

Note the asymmetry in how the two defects surface.  An over-strong
hypothesis is found by *reading* — nothing breaks, so nothing prompts
you.  An under-strong one is found by *using* — the first consumer that
needs the missing fact cannot be written.  The under-strong kind is
therefore self-correcting and the over-strong kind is not, which is why
§8.2's tells matter more than this one's, and why the two sections are
**not** a matched pair deserving equal vigilance.  §8.2 states the same
asymmetry from its side; if you are budgeting attention, spend it
there.

**Open redundancy, recorded so it is not forgotten.**
`Expr.LeavesBounded e` may be implied by `CtxOk`: the leaf clause
already gives `denote … l.2.2 = some …` for every leaf, and if
denotation success implies `looseBVarsBounded 0` then `LeavesBounded`
is free.  That implication looks true — `denote` sends `.bvar` to
`none` and opens binders with `fvar`s — but proving it needs a converse
of `looseBVarsBounded_instantiate1`, which does not exist yet.  Two
lemmas to remove one hypothesis; deferred, not dismissed.  It is a
redundancy question, not an over-strength one: the proofs do read
`LeavesBounded`.

### 8.3 The extension layer is complete

Every `EnvTT` field now has its `.cons`, and `EnvTT.cons` assembles
them: it takes the head obligations for the constant being installed
and returns the invariant for the extended environment.  That is the
whole of what the `checkDecl` case analysis will consume from this
side — obligations are stated *only* for the new constant, and clauses
about already-stored constants are discharged once here rather than
once per case.

Three things made it cheaper than the model's equivalent.

**The guards are monotone, not merely congruent.**  A guard that holds
has already *found* every slot it reads, so each slot is `isSome` in
the small environment and freshness supplies the distinctness.
`natLitSupported_cons` / `strLitSupported_cons` / `natOpGuard_cons`
therefore take one hypothesis, and `Installs.denoteUp` takes none —
where `denote_mono` needs two.  The congruence lemmas (which need the
distinctness as input) stay for the basis install, which is the one
case where the new constant really is one of those slots.

**`Installs` bundles the install context**, with `denoteUp`,
`denoteDown`, `agree` and `find` as its API.  It describes an
*ordinary* install; a basis install is exactly what violates its last
three fields, and is exactly the thing that can change what a literal
denotes.  That is the honest division rather than a convenience one.

**`DivModTT` needed no new hypothesis.**  Every name its clauses read
is pinned by `natOpGuard` — which is what the dependency list is *for*.
The nine branches are written out because the dependency lists differ
per operation; nothing else about them differs.

`denote_params_ext` completes the family of "what the denotation
reads" lemmas — `denote_mono` (environment grows), `denote_env_shrink`
(environment shrinks, for stored terms), `denote_cval_congr`
(valuation changes), and now the level assignment.  It is the fact an
install needs to store `⟦value⟧` as the new constant's valuation and
still satisfy `val_params`, so it is a prerequisite of every case, not
just of the definition cases.

Its literal clauses want to know that the literal-support constants
carry no level parameters, and they take that from the **branch
condition** rather than from an inversion lemma: `denote` only builds
`natLitT` when `natLitSupported` holds, and the guard's own shape
checks say `levelParams.isEmpty`.  `List.nil`/`List.cons` are the two
slots that do have a parameter, and there the substituted level is
`Level.zero`, which no assignment can see.

### 8.4 The guards carry what the denotation needs

Three proofs now discharge an environment fact from a **branch
condition** instead of an inversion lemma:

1. the guard congruences and their monotone forms — a guard that holds
   has found every slot it reads;
2. `DivModTT`'s transport — every name `DivModClausesTT` reads is in
   `natOpDeps c`;
3. `denote_params_ext`'s literal clauses — the support constants'
   `levelParams.isEmpty` comes from `natLitSupported`'s shape checks.

This is not three conveniences.  It is the checker and the denotation
**agreeing about which constants matter**: a guard exists to pin
exactly the constants the corresponding denotation clause reads, so
whenever a clause fires, its guard has already established everything
that clause's meaning depends on.

**Why the count keeps rising** (six instances at the time of writing —
the guard congruences, `DivModTT`'s transport, `denote_params_ext`'s
literals, `denote_instLevels`'s literals, `strLitSupported`'s ten
pinned types, and #129's projection entry).  It has stopped being a
pattern and become a property of the design, and the property is one
sentence:

> **The pins exist so the *checker* can compare against known shapes,
> and the same pins are why the *bridge* can compute against them.**

A pin is a commitment that a declaration has an exact form.  The
checker uses it to decide acceptance without inspecting a value; the
bridge uses it to denote without inspecting one either.  Neither use
was designed for the other, which is why each new pinned family
produces a clause that is mechanical rather than a clause that needs
an argument — and why the right first move, at any new obligation about
a stored constant, is to read its guard.

**Confirmed prospectively, which is what makes it a tool.**  The rule
was written down after three retrospective sightings.  Its fourth use
was the first *prospective* one: `denote_instLevels`'s literal clauses
were expected to need `natLitSupported_inv`, the rule said to look at
the guard instead, and the guard's own shape checks supplied
`levelParams.isEmpty` directly — the `cval_of_isEmpty` helper built for
`denote_params_ext` applied unchanged.  An observation that is checked
after the fact is a pattern; one that is applied before the work and
holds is a tool, and the difference is worth marking.

**What it predicts**, which is the reason to write it down rather than
note "we used the guard" three times: *for any future obligation about
a constant that a `denote` clause reads, look first at the guard that
gates that clause, not at an inversion of the environment.*  The
inversion lemmas (`natLitSupported_inv`, `natOpGuard_inv`) recover a
guard's consequences from the guard; the guard itself is the cheaper
thing to want, and so far it has always sufficed.  Concretely: the
`indDecl` case will need facts about a modeled family's stored
artifacts, and the first place to look is the install-time check that
gated storing them.

A corollary worth stating because it cuts the other way: the bridge has
so far needed **none** of the four `V`-free inversion lemmas stranded
in `Setlec/Model/*`.  If that holds to the end, the relocation task
shrinks from "move them" to "they were only ever needed by the model".

A gotcha worth one line, because it cost time and gives no useful
error: in `rcases hc with _ | ⟨-, hc⟩` on a `List.Mem`, the `-` clears
the *head element* of the list — here `c₀` — and with it every
hypothesis mentioning `c₀`.  The symptom is "unknown identifier
`hi.fresh`" several lines later, pointing at the use rather than the
cause.  Use `_`, not `-`, for a constructor argument that other
hypotheses depend on.

### 8.2 "Too strong" is the recurring defect, not "too weak"

Three instances in three increments, all found by reading a statement
rather than by a proof failing:

1. `denote_cval_congr` first took agreement at *all* names, which
   subsumes its own conclusion — the vacuity bug, caught because it
   compiled first try (§0).
2. `denote_mono`'s level-parameter hypothesis was quantified over all
   names when the proof reads exactly two (`listNilName`,
   `listConsName`).
3. `RecRulesTT`/`NatOpsTT` were given `constsResolve` clauses that
   `EnvWF` already supplies, so the field asserted content it did not
   own.

None of these is a soundness hole — an over-strong hypothesis makes a
lemma *harder* to apply, not wrong — which is exactly why they survive
review: nothing breaks. They surface later as transports that will not
go through, or as fields nobody can discharge.

**These tells matter more than §8.5's, and the reason is an asymmetry
worth stating explicitly** — see §8.5, and do not read the two sections
as a matched pair:

> An **over-strong** hypothesis is found by *reading*.  Nothing breaks,
> so nothing prompts you; it is silent forever, and only deliberate
> vigilance finds it.
> An **under-strong** hypothesis is found by *using*.  The first
> consumer that needs the missing fact cannot be written, so it
> announces itself.

The under-strong kind self-corrects on contact.  The over-strong kind
does not.  Spend the vigilance here.

**The default when writing a hypothesis: ask what the proof actually
reads, not what would obviously suffice.**  "Obviously suffices" is how
all three arose.

**The three tells, sorted by whether a tool covers them** — which is
the practical question, because it says where reading is the only
option:

| tell | caught mechanically? |
|---|---|
| quantified more broadly than the conclusion needs | **sometimes** — only if the excess makes the binder *unused*, which the unused-variable linter flags every time and for free |
| subsumes the conclusion | **never** — the hypothesis is genuinely consumed, so nothing complains |
| duplicates a clause an adjacent field carries | **never** — likewise consumed |

The instance that produced this table: `Deq.close1` carried a
closedness hypothesis copied from `Deq.close2` and never used it; the
linter flagged it on the first build.  The instance that shows the
limit: `denote_cval_congr`'s "the valuations agree everywhere" was
*used* by its proof, so no linter would ever have flagged it — it took
noticing that the proof compiled first try.

This sharpens §8.5's asymmetry rather than replacing it.  Over-strong
is the dangerous class *because* it is silent — but one corner of it is
not silent, and knowing which corner is where the attention should go.
**Run the linter and read the hypotheses; neither substitutes for the
other.**

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

## 9. A constraint on task #117 (recorded here because nowhere else has it)

Task #117 plans to eliminate the input-normalization pass; its item 4
moves the projection rewrite from a stored pass to an implicit step at
typecheck/reduction time.

**Reduction currently depends on that pass.**  `whnfCoreBody`'s
`.proj` clause reads the structure name off the *node* —
`env.findProj? sn i` where `sn` comes from `.proj sn i pe` — and never
infers the subject to obtain it.  What makes that sound is an
invariant the **annotate** pass establishes: its own `.proj` clause
infers the subject, whnfs the type, and *normalises the node's `sn` to
that type's head* (`Setlec/Kernel/Core.lean`, `annotateBody`).

So #117 must either **preserve that invariant by another route** or
**establish it at the point of use** — i.e. have the `.proj` reduction
determine the structure from the subject's own type rather than
trusting the node.  The second is closer to what the reference kernels
do, and it composes well with the separate finding of §6 (the clause
also needs a telescope certification of the constructor spine): both
are checks *at the point of use*, and a redesign that adds one may as
well add the other.

Recorded as a constraint on the design, not as an observation about
today's clause: whoever picks up #117 needs it *before* designing, and
until now it existed only in this task's working notes.

## 10. Changes this bridge asks for

A different *kind* of output than the rest of this document: not
verification results but design requests, each needing its own branch,
gates and measurement.  Three so far — two to the checker, one to the
layer.  The third (§10.3) is **open**: it is a request, not a decision
I may take.

**This is a steady product of the work, not two incidents.**  Both came
out of the same operation — *take a rule's premises; ask which call
establishes each, at the rule's own domain* — and that operation reads
the checker and the layer against each other.  A bridge that only
consumed both sides would produce neither request: it is the
*confrontation* that finds a checker certifying less than a rule needs
(§10.1) and a rule demanding more than its soundness uses (§10.2).
Expect more of these, and expect them to land on either side.

### 10.1 To the checker: certify the projection's constructor spine

**The `.proj` clause of `whnfCoreBody` should certify the
constructor's spine against the constructor's telescope**, exactly as
`iotaRec` already does — an `iotaCerts` on
`cvj.type.instantiateLevelParams cvj.levelParams us` against
`e'.getAppArgs`.

*Why.*  The reduction `proj_i (C p⃗ x⃗) ↦ x_i` is justified in the layer
by `projFstMk`/`projSndMk`, whose premises are the four telescope
domains of `PSigma'.mk`.  The clause currently runs `projCert`, which
checks *levels* (the collapse guard) and supplies none of those four.
So a derivation cannot be rebuilt from what the checker records.

*What it is not.*  Not a soundness bug: nothing suggests the reduction
is wrong.  The checker simply does not write down enough for the bridge
to reconstruct a derivation.  Expected cost is one call on a path that
already runs `projCert`, and `iotaCerts` on a four-element spine is
small; but it is a kernel change and must be measured, not assumed.

*Status.*  **Landed** (task #126).  Measured **+0.145 % certified,
0.00 % cert-skipping**, byte-identical in both modes, no verdict moved
— so the "must be measured, not assumed" caveat resolved in the cheap
direction.  The cert-skipping mode deliberately skips the new call, on
the grounds that a mode skipping three telescope certifications and
keeping a fourth reports a meaningless number; the rationale is in the
top-level `DESIGN.md`.

What the bridge gets: `projTeleCert_inv` turns a successful run into
the constructor's stored type plus the `iotaCertsP` fact — **the direct
entry point for `certs_typed`**, so the premises arrive as premises
rather than as a call to replicate.  `whnf_proj_inv` grew a final
conjunct for it.

(That the merge cost this branch no mechanical fixes is **timing luck,
not a free interface**: the bridge simply had no `whnf_proj_inv` call
sites yet.  A branch that did would have paid the usual
pattern-match update.)

### 10.2 To the layer: the irrelevance rules are over-constrained

Found while proving `majorToCtor`'s **K branch**, and it is the same
defect twice.

`majorToCtor`'s K rescue certifies its fabrication with
`proofIrrel r env depth fab major`, which checks that **each side's
type is a `Prop`** — `whnf (infer ta)` and `whnf (infer tb)` are both
`.sort ≡ 0` — and *not* that the two types are the same.  The layer's
`HasType.proofIrrel` demands one `P` for both:

```
Γ ⊢ P : Sort 0 → Γ ⊢ h : P → Γ ⊢ h' : P → Γ ⊢ prf : eqE P h h'
```

The unit-like branch has the identical shape: `proofIrrel`'s first
branch accepts when `isUnitLikeTy` holds of each side's whnf'd type
*separately*, and `isUnitLikeTy` matches `.const c _` — **ignoring the
levels** — so `a : PUnit.{3}` and `b : PUnit.{5}` both pass.  The
layer's `punitEta` requires both subjects at `punitT u` for the *same*
`u`.

**Both rules are over-constrained relative to their own soundness
proofs**, which is a §2.4 violation in the harder-to-spot direction:
not a premise soundness ignores, but a *coincidence* — "the same
type" — that soundness never uses.  `proofIrrel`'s soundness applies
`mem_univ_zero` to each side independently; `punitEta`'s reads
`mem_unitSet` of each side, and `bval .punit us = unitSet` ignores
`us` entirely.  So both generalize soundly:

```
proofIrrel : Γ ⊢ P : Sort 0 → Γ ⊢ Q : Sort 0 → Γ ⊢ h : P → Γ ⊢ h' : Q → …
punitEta   : Γ ⊢ x : PUnit.{u} → Γ ⊢ y : PUnit.{v} → …
```

*Why not derive it instead.*  Across two different **inhabited**
`Prop`s the equation *is* derivable — `propext` gives `Deq [] P Q`,
`conv` retypes `h'`, and `proofIrrel` then applies at one `P`.  But
building `propext`'s two implications needs
`Γ ⊢ e : A → (B :: Γ) ⊢ e↑ : A↑`, i.e. **binder weakening**, whose
`app` case needs lifting to commute with instantiation — the
substitution algebra §7 was built to avoid.  Paying that to work around
an over-constrained rule would be the wrong trade twice over, and its
cost is itself the argument for the generalization.

*Status.*  **Landed** on `feat/74-relax-premises`, with the layer's own
axiom gate unmoved.  The soundness cases changed by **one identifier
each** — the number to quote if the relaxation is ever questioned.

**The loop closes, and it closed cleanly.**  The first consumer written
after the change, `proof_irrel_step`
(`Setlec/TTVerify/Iota.lean`), needed **precisely** the freedom the
change added — the two typings at *different* types — and nothing more.
Before the change the lemma could not have been *stated*.  That is the
cleanest validation a relaxation can get: request, change, and a
consumer showing the request was right-sized rather than convenient.

**And the negative half, which is the precedent.**  The proof needed no
`propext`, no binder weakening, no substitution algebra.  The
workaround was priced at three lemmas plus a commutation stack; the
generalization made it two lines.  *That comparison is the argument for
asking the layer for a change rather than working around it*, and it is
the precedent for the next time this bridge meets an over-constrained
rule: **price the workaround first, and if it exceeds the change,
ask.**

**But the rule does not transfer to requests against the *checker*, and
the asymmetry is worth stating so the precedent is not
over-applied.**  It works here because the layer is an **upper bound**
(§2.1): a *sound* relaxation is a weaker obligation on the bridge and
cannot change any verdict, so its cost really is just the edit.  A
checker change can move verdicts, and must earn its way past
byte-identity and a measurement.  Compare the two requests:

| | layer (§10.2) | checker (§10.1) |
|---|---|---|
| can move verdicts | **no** (upper bound) | **yes** |
| gate | the layer's axiom check | byte-identity + arena/e2e + measurement |
| cost found | one identifier per soundness case | +0.145 % certified, 0.00 % NC |

So: against the layer, price the workaround and ask if it loses.
Against the checker, price the workaround *and* the measurement, and
expect the burden of proof to sit with the request.

## 11. DECIDED: how the pinned `Eq` block denotes

The mismatch is inherent, not accidental: `eqE` **must** be a syntactic
former because `conv` pattern-matches on it — equality reflection
requires that — while the checker has `Eq` as an ordinary pinned
inductive **constant**, which can appear partially applied.

### The measurement that settled it

Two candidates: denote the bare constant as its **eta-expansion**, or
**special-case the spine** `@Eq A a b` in `denote`'s `.app` clause.
Counting occurrences in real input (graph walk over the export's
hash-consed expression table, since arity is not greppable):

| stream | `Eq` fully applied | **partially applied** |
|---|---|---|
| init-prelude (preprocessed) | 1942 | **1** |
| all 36 e2e fixtures containing `Eq` | many | **0** |

**So the spine special-case would have passed the entire e2e suite and
failed only on the real stream.**  One occurrence in ~2000 is exactly
the density that makes "it never happens" feel safe and be wrong, and
it is why this was worth measuring rather than assuming.

### The decision

**Denote the bare constant as its eta-expansion**, and state the field
as a *fired law* rather than as a pinned valuation — matching
`rec_rules` and `caps_ok`:

> for `A, a, b` typed at the `Eq` telescope's domains,
> `Deq Δ (mkAppN (cval eqName ψ) [⟦A⟧, ⟦a⟧, ⟦b⟧]) (eqE ⟦A⟧ ⟦a⟧ ⟦b⟧)`.

The law is what consumers need; the eta-expansion
`lam (sort u) (lam #0 (lam #1 (eqE #2 #1 #0)))` is the natural witness
at the pinned block's install, and partial applications denote to it
correctly because `denote` never has to know the arity.

Three independent reasons, of which the first alone is decisive:

1. **Empirical** — partial application occurs, so the special-case is
   incomplete on the corpus we actually check.
2. **Principled** — a spine special-case is a *computing* clause in
   `denote`, breaking the structural rule of §2 that §7's accounting
   (four substitution lemmas, not six and climbing) depends on.
3. **Precedent** — it is how the layer already relates a former to the
   constants it replaces: `psigmaFst`/`psigmaSnd` became lambdas over
   the `proj` former and left `BConst` (`Setlec/TT/DESIGN.md` §3).

*Cost, and where it is paid.*  Converting a spine to the former takes
three `beta` steps, each wanting `⊢ arg : dom`.  Those come from the
**app-argument certificate**, which §6 has already established is
permanent.

**So read this as no cost at all.**  "Three `beta` steps" sounds like a
price until you notice the supplier was already paid for: this is a
*third consumer* of a certificate the checker runs regardless and that
the bridge cannot do without.  A cost that reuses an existing,
unavoidable obligation adds nothing to the total — and the same reading
applies to any future clause whose premises land on that certificate.

### The block's other constants

* `Eq.refl` — the analogous lambda over the layer's canonical proof
  (`prf` at an `eqE`), by the same argument.
* `Eq.rec` — **nothing new needed**: `eqRec_derivable`
  (`Setlec/TT/Examples.lean`) already exists, from the `congrEq` work.

## 12. The governing design directive, and what it changes

A user directive arrived before `DefEqClaimsTT` and `InferClaimsTT`
were proved (they were already *stated*).  Most of it codifies where
this bridge had already converged; two parts change the plan, and one
part I have to report a conflict about rather than silently resolve.

**The directive, in the terms that bear on this file.**  Verification
is factored through the TT layer: every step of the pure checker is
justified by a direct correspondence to a TT rule.  The bridge's only
jobs are translating imperative code to an inductive relation, moving
irrelevant decisions out of view, and removing features by
interpretation.  The checker and the rules should be close enough that
the bridge does nothing clever — thread an induction with a suitable
invariant, case split, apply the right rule.  **Rules need not be
premise-free**: premises may follow from guards/branches in the
checker, or from *preconditions*.  `infer` gets no precondition (it is
the establisher); `whnf` and `isDefEq` are **welcome to** assume their
input well-typed.

### 12.1 §2.4 is scoped, not retracted

The premise-free discipline in `Setlec/TT/DESIGN.md` §2.4 governs the
**layer's equational rules**, and it stands — it is why the
substitution metatheory is two semantic lemmas rather than 123
syntactic ones.  The amendment is one level up: **the bridge's claims
may carry preconditions**, supplied by the checker's guards or by
callers.  Two different objects, two different disciplines; conflating
them would have made the directive look like a reversal, and it is not.

### 12.2 The `defeq` call-site map

Every `defeq` call in `Setlec/Kernel/Core.lean`, by what the caller
holds and what it needs.  Two roles:

**(A) Certificate calls** — the caller has just *inferred* one side and
holds an annotation for the other; it needs the argument typed at the
annotation.

| site | shape | needs |
|---|---|---|
| `iotaCerts` (733) | `ta ← infer arg`, `defeq ta ty` | `⟦arg⟧ : ⟦ty⟧` |
| `whnfCore` β (1346) | `ta ← infer a`, `defeq ta ty` | `⟦a⟧ : ⟦ty⟧` |
| `inferBody` app (1529) | ditto | ditto |
| `inferBody` let (1563) | `tv ← infer v`, `defeq tv ty` | `⟦v⟧ : ⟦ty⟧` |
| `majorToCtor` K (1047) | `defeq tmaj (infer fab)` | both sides `Prop` |

All five want the same thing: a `Deq` between **types**, consumed by
`conv`.  None of them needs the two sides *typed*; they need the
equation.

**(B) Internal recursion** — `defeqStep`'s own descent: pi congruence
(1757), spine congruence (1784), projection congruence (1794),
`defEqList` (751), literal folds (1719/1736), the eta rescue (956),
the unit-like rescue (935), pair eta (819), lazy delta, `stuckIrrel`.
These are where a contract has to be *maintained*, so they decide it.

### 12.3 The three contracts: (1) and (2) are refuted

> (1) `isDefEq a b → ∃ T, [a] : T ∧ [b] : T ∧ eq(T,[a],[b])`
> (2) `isDefEq a b → ∀ T, [a] : T → [b] : T ∧ eq(T,[a],[b])`
> (3) `isDefEq a b → ∀ T, [a] : T → [b] : T → eq(T,[a],[b])`

**Contract (1) is refuted by the checker's own de-gating.**
`defeqStep`'s `forallE` clause compares the domains and the opened
bodies and **nothing else** — task #100 stage 3 deliberately removed
the binder-annotation comparison, because the collapse model's
`piC_congr` needs only the domain and fibre agreements.  So the checker
accepts `∀x:A₁.B₁ ≡ ∀x:A₂.B₂` with `A₁ : Sort u`, `A₂ : Sort v` and
`u ≠ v`; the two pis then live at `Sort (imax u v₁)` and
`Sort (imax v v₂)`, and contract (1) demands a **common** `T` for them.
Nothing establishes it, and the layer has no unique typing to recover
it from.  Not provable — and, on the same witness, plausibly false.

Worth naming: this is the *second* time a checker simplification has
constrained the bridge's statements (the first was the beta certificate
becoming unconditional).  A de-gating removes work from the checker and
moves an obligation to whoever wants a stronger contract from it.

**Contract (2) is refuted by F1.**  Deriving `[b] : T` from `[a] : T`
across `a ≡ b` is *subject* conversion.  `HasType.conv` moves the type,
never the subject, and no other rule concludes a typing whose subject
was moved.  That is F1 exactly (§6), and the same refutation that
killed the threaded claim shape kills contract (2).

**Contract (3) is adopted — and the bridge proves something
stronger.**  `DefEqClaimsTT` concludes `Deq Δ va vb` with **no typing
hypotheses at all**, which implies (3): `Deq.toHasType` re-slots an
equation at any type, because `eqE`'s type argument is inert (it is
carried for the denotation and never checked — `Setlec/TT/Syntax.lean`).

That inertness is the reason the choice is cheap rather than
consequential: **the equation carries no typing**, so the three
contracts differ only in where the *typings* sit, and the bridge's
answer is "nowhere — they are not needed".

### 12.4 The conflict I am reporting rather than resolving

The directive permits `whnf` and `isDefEq` to assume well-typed input.
**On the evidence of the call-site map, neither needs it.**  Every rule
premise either of them must discharge is already supplied at the site:

* `HasType.beta`'s premise — the β certificate (1346), proved;
* `HasType.eta`'s premise — the guard `tb ← infer b; whnf tb = ∀…`;
* `UnitLawTT` / `EtaLawTT` premises — the guards at 935/956;
* proof irrelevance — the two sort guards, proved (`proof_irrel_step`);
* pi / app / proj congruence — `Deq`'s congruence lemmas are
  premise-free;
* delta — no premise, because it is an identity (§2);
* the literal folds — the `natOpGuard` guards (§8.4).

That is §6's headline fact reasserting itself from the other side: *the
certificates are the reason a precondition is unnecessary.*  A checker
without them would need one.

So I have **not** added `Typable` preconditions to `WhnfCoreClaimsTT`,
`WhnfClaimsTT` or `DefEqClaimsTT`.  Adding a hypothesis no clause reads
is precisely §8.2's over-strong defect, and I would be committing it in
the increment that records §8.2.  If a clause turns out to need one,
the directive sanctions adding it and `Setlec/TTVerify/Typable.lean` is
ready; the statement change is local.

**`InferClaimsTT` is already in the sanctioned form**: no precondition,
and its conclusion *is* "successful inference establishes typing".

### 12.5 What was built anyway, and why it is not wasted

`Setlec/TTVerify/Typable.lean`: the predicate and the inversion family
(`appFn`, `appArg`, `projSubj`, `lamBody`, `piDom`, `piCod`, `letVal`,
`letBody`).  It is on the critical path for the *next* thing the
directive names — the `InferOnly` relation, where the precondition is
essential rather than optional, because `infer_only` skips the argument
check and `Typable e → InferOnly e t → e : t` is the only way to get it
back.  The count-to-four alarm (`Setlec/TT/DESIGN.md` §3.1) is
**superseded for this family and this family only**: one member per
former is the plan, not erosion.

Three gaps in the family are structural and are recorded at the module:
`lam` yields the body but not the domain (the rule has no domain
premise); `eqE` yields nothing (`eqType` is premise-free); `letE`
yields the **substituted** body (matching its rule — the layer never
types the open one).

### 12.6 Re-examining the three obligations: the answer is "no shrink"

The directive asks whether a `Typable` precondition discharges frame
conditions the obligations were about to prove by hand.  **It does
not, and the reason is a type error rather than a judgement call:**
the frame conditions (`WScoped`, `looseBVarsBounded`, `LeavesBounded`)
are facts about the **`Expr`**; `Typable Δ ⟦e⟧` is a fact about the
**`VExpr`** it denotes to.  A denotation forgets exactly the syntax the
frame conditions constrain — `.fvar idx n ty` denotes to `.bvar _`
whatever `idx` and `ty` are — so no amount of typing on the far side
says anything about scoping on the near side.

That is worth stating positively rather than as a disappointment: it is
the same separation that makes the bridge work at all.  The syntactic
conditions travel with the checker's own preservation lemmas
(`whnfCore_WScoped` and friends, all in `Setlec/Verify/*`), and the
semantic ones travel with the certificates.  Neither can substitute for
the other, and a design where they could would be one where the
denotation leaked syntax.

**`ReduceNatStepTT` is discharged** (`Setlec/TTVerify/NatOpsStep.lean`),
and it is the case that shows the separation cleanly: its frame half
was free — the reduct is a literal or a `Bool` constructor, so
`reduceNat_inv` gives it in three lines — while its equation half took
sixteen closed forms.  Two of three obligations remain, both frame
bookkeeping around equations that are already proved.

### 12.7 Correction: "frame bookkeeping" understated `IotaStepTT`

I described the two remaining `whnfCore` obligations as "frame
bookkeeping around equations that are already proved".  That is right
for `ProjStepTT` and **wrong for `IotaStepTT`**, and since it was
repeated back to me in planning it needs correcting rather than
quietly fixing.

What `iotaRec_inv` actually hands back is a chain, not a redex:

```
e's major  --whnf-->  major₀  --litMajorToCtor-->  major₁
           --majorToCtor-->  major (in constructor form)
```

and only then does the stored rule fire.  `rec_rules_fire` is proved
**at the fired form** — it takes the constructor-form major as given.
So `IotaStepTT` additionally owes the soundness of that chain: that
each step preserves the denotation up to `Deq`.  Its rescues are proved
(`eta_rescue`, `proof_irrel_step`), but the *assembly* — the plain
case, the literal case, and the dispatch between them — is not.  The
set model spends `Setlec/Model/Core/MajorToCtor.lean` (550 lines) plus
`NestedFire.lean` (511) on exactly this.

**What I got wrong and why**: I inferred the size from what the
obligation's *statement* mentions (a reduct and its frame conditions)
rather than from what its *proof* must traverse.  A statement that
names two terms can still hide a four-step chain between them, and
`iotaRecP` is one call in the inversion's premise.  The general form:
**estimate an obligation from the checker function it inverts, not from
the shape of its conclusion.**

Revised decomposition, which also improves the promise boundary per
§8.6 (fewer unproved steps outside the obligation):

* `MajorToCtorStepTT` — the chain's soundness, a new named obligation;
* `IotaStepTT` — provable from it plus `rec_rules_fire`, plus frame
  conditions of which `iotaRec_WScoped` supplies one of three;
* `ProjStepTT` — unchanged, and genuinely the smaller of the two.

### 12.8 The `infer` quarter, assembled

`InferClaimsTT` at `fuel + 1` is proved
(`Setlec/TTVerify/InferStep.lean`), modulo two clause-granularity
obligations (`InferStrLitStepTT`, `InferProjStepTT`).  Nine of eleven
clauses are complete, and the assembly is eleven lines of dispatch.

**That the assembly is eleven lines of dispatch is the directive's
claim, checkable.**  The directive says the checker and the rules
should be close enough that the bridge does nothing clever — thread an
induction with a suitable invariant, case split, apply the right rule.
The `infer` quarter is where that is most visible, because `inferBody`
has one clause per former and each clause is one rule:

| clause | rule | what supplies the premise |
|---|---|---|
| `.sort` | `sort` | — |
| `.fvar` | `bvar` | `CtxOk`, and the index arithmetic *is* `CtxOk`'s |
| `.const` | `EnvTT.has_type` | the environment invariant |
| `.lit natVal` | `hasType_numeral` | `basis_pinned` |
| `.forallE` | `pi` | two IHs and `ensureSort` |
| `.lam` | `lam` | one IH — the rule has no domain premise |
| `.app` | `app` | the IH for the head, the **certificate** for the argument |
| `.letE` | `letE` | `ensureSort`, the certificate, the IH on the *substituted* body |
| `.bvar` | — | refuted from the denotation |

Three observations worth keeping.

**The `.app` clause is §6 in four lines.**  Two induction hypotheses,
two `conv`s, one rule; the argument's typing is re-established at the
domain the redex names.  Nothing is threaded and nothing is inverted.

**The `.letE` clause is where the layer's `letE` choice pays.**
`HasType.letE` types the *substituted* body, and `inferBody` recurses
on exactly that — so neither side opens the binder and the clause needs
no substitution lemma at all.  The recorded finding that opening a
`let` body with an opaque variable is too weak for real streams shows
up here as an *absence* of work.

**The `.lam` clause reads a guard the layer does not want.**  The
checker checks `whnf (infer ty)` is a sort; `HasType.lam` has no domain
premise, so the bridge never consumes it.  That is
`Typable.lamBody`'s gap (§12.5) seen from the producing side — the same
asymmetry from the other end, and a small confirmation that the gap is
the layer's discipline rather than an oversight.

One lemma had to be added, and it is the one place §12.6's separation is
crossed **deliberately**: `denote_bvarsBelow` — a term scoped below
depth `d` denotes to a `VExpr` whose bound variables are below `d`.
That direction holds (an `fvar` at `idx < d` denotes to
`.bvar (d-1-idx)`); the converse, typing telling you about syntax, is
the one that does not.  It is what lets the `.const` clause move
`EnvTT.has_type` from the empty context at depth 0 to `Δ` at depth `d`,
using the same `denote_instLevels` and `denote_lift` the delta step
needed — the same fact about `cval`, read in two directions.

### 10.3 OPEN REQUEST: `inferBody`'s `.proj` clause needs the parameters' sorts

**The gap.**  `HasType.projFst` and `HasType.projSnd`
(`Setlec/TT/Judgment.lean`) each carry three premises:

```
⊢ A : Sort u      ⊢ B : A → Sort v      ⊢ p : PSigma' u v A B
```

`inferBody`'s `.proj` clause supplies only the third.  It computes
`te ← whnf (infer pe)`, checks `te.getAppFn` is a stored constant with
a native projection entry, checks the parameter count and the level
count, and reads the residual off the entry's pinned type.  It never
infers a sort for either parameter.  So the bridge can produce
`⊢ ⟦pe⟧ : psigmaT u v ⟦A⟧ ⟦B⟧` and **cannot** produce the other two.

**The rule is not over-constrained.**  This is *not* the
`proofIrrel`/`punitEta` situation of §10.2, and I checked before
concluding: `Setlec/TT/Semantics/Soundness.lean`'s `projFst` case
consumes both — `psigmaV_app V hAm hBm` needs them to unfold the
psigma set and `sfst_mem V hAm hpm` needs the first again.  The layer's
§2.4 doctrine is satisfied; the premises are real.

**The workaround was priced first (§10's own rule) and does not
exist.**  What is available is an *inhabitant* of `psigmaT u v A B`.
Recovering the parameters' typings from it means inverting the type
former's application — the same shape as Π-domain-injectivity, which
§6 records as inadmissible.  `Typable` does not help either: it is
inversion on the **subject**, and here the subject is `pe`, whose
subterms tell us nothing about `A` and `B`.  There is no field of
`EnvTT` that could carry it: `A` and `B` are arbitrary terms appearing
in an inferred type, not stored data.

**The request.**  `inferBody`'s `.proj` clause should certify the two
parameters' sorts, in the same style as the β certificate and as task
#126's `projTeleCert`: infer each parameter's type and `ensureSort` it,
at the levels the entry pins.  That is two extra `infer` calls and two
`ensureSort`s per projection *inference* (not per reduction — the
reduction path already has `projCert` and `projTeleCert`).

**Why I am asking rather than taking it.**  §10 records the asymmetry
deliberately: a request against the *layer* may be taken when it brings
the layer into line with its own doctrine, because the layer is an
upper bound and a relaxation cannot make the bridge claim more.  A
request against the *checker* changes what is accepted, so it needs
measurement (verdicts, NC rate, byte-identity) and is not mine to
decide.  The measurement to run, if it is granted, is the one #126
used: certified fraction, NC rate, and init-prelude byte-identity.

**GRANTED and landed as task #129** (+0.102% certified, 0.00% NC,
byte-identical both modes).  `InferProjStepTT` is discharged and
`InferClaimsTT` is closed.

**The implementer's shape is better than the one I asked for**, and the
correction is worth recording because it is §10.1's own law applied
against my request.  I asked for two `ensureSort`s.  What landed is
**one `iotaCerts` telescope walk on the entry's stored type**, because:

* `⊢ B : A → Sort v` is not a sort judgement at all, so `ensureSort`
  cannot express it;
* an `ensureSort` on `A` would land at the level the checker
  *infers*, while `projFst` names the level the entry *pins* — the
  premise would arrive at the wrong domain.

The telescope walk delivers both premises at the domains the rule
names, because the first two binders of `pairFstTyA` are literally
`Sort u` and `α → Sort v`.  So the clause is the same shape as
`proj_tele_typed` one level up: `projParamCert_inv` → `certs_typed` →
destructure the walk → apply the rule.

**The lesson for future requests**: I priced the workaround and named
the gap correctly, but specified the *mechanism* from the shape of the
premises rather than from the shape of the rule's domains.  §6's
headline fact says where premises must be supplied; it also says what
they must be supplied *at*, and a request should name the domain, not
the tactic.

### 12.9 §8.1's rule, read in the other direction

Found while assembling `IotaStepTT`, and it is a correction to how I
had been applying §8.1 rather than to §8.1 itself.

The rule says: *facts about arbitrary expressions may appear only in a
law's conclusion; facts about **stored** expressions may be
hypotheses, because they transport.*  That is a statement about what is
**permitted**, and I had been reading it as a statement about what is
**preferred** — putting stored-expression facts in the premise wherever
the rule allowed it.

`RecRulesTT` is where that bites.  Its rule right-hand side's
denotation is a fact about a stored expression, so §8.1 permits it as a
hypothesis, and that is how the restatement left it.  But **no caller
can discharge it**: a stored `Expr` being closed and
`constsResolve`-clean does not make its denotation `some` — a `.const`
at the wrong level arity denotes to `none`, and nothing in `EnvWF`
rules that out.  The fact is establishable only at *install*, which is
exactly where an invariant's conclusions are established.

The set model, facing the same choice, made it the other way:
`RecRulesOk` concludes `∃ Rv, interpClosed … = some Rv ∧ …`.  That is
the third time reading the model's shape has corrected the bridge's,
and the pattern in all three is the same — the model's field is the
answer to "what must the install prove?", and the bridge's is the
answer to "what may the fire site assume?", which are the same question
only when the fire site can prove what it assumes.

**The rule as it should be quoted**, then:

> Facts about arbitrary expressions must be conclusions.  Facts about
> stored expressions may be hypotheses **if some caller can establish
> them** — and if none can, they belong in the conclusion too.

The change itself (field, transport, fire site) lands as one commit;
the transport gets *easier*, since a produced denotation moves forward
with `Installs.denoteUp` where a hypothesised one needed `denoteDown`.

### 12.10 The iota assembly, and a second clause the field was missing

`IotaStepTT` is proved (`Setlec/TTVerify/IotaStep.lean`), modulo the
chain's two links.  The assembly is `iotaRec_inv` → split the spine at
the major → run the three-link chain → `rec_rules_fire` → reassemble,
and the only step that is not bookkeeping is the last `Deq`: the redex
as written and the redex with its major in constructor form differ in
**one spine position**, so `VExpr_mkAppN_snoc` and `Deq.appArg` bridge
them.

Writing it surfaced a second missing clause, by the same route as
§12.9's: the reduct is `rhs` applied to `e.getAppArgs.take rP ++ …`,
and identifying that prefix with the certified spine needs `rP ≤ mI`.
`EnvWF` has it **only for nested rules**; `RecRulesOk` has it for every
fireable one.  So `RecRulesTT` gained it, and the pattern is worth
naming because it is now three for three:

> **When a clause is missing, the model's corresponding field already
> has it.**

`RecRulesOk` has four clauses the bridge's transposition initially
dropped as "not needed by the fire site" — the `AnnotOk` one genuinely
is not (no counterpart), but the other three were needed and had to be
put back one at a time, each discovered by an assembly that could not
close.  The lesson is not "copy the model", which §0 already says; it
is sharper: **a field's clause list is a claim about what installs
must prove, and dropping one is a claim that no consumer needs it —
which is only checkable by writing the consumer.**  Transposing a
field is therefore not finished when it typechecks; it is finished when
its consumers do.

**And the discipline discriminates rather than merely conserves**,
which is the part that makes it worth having: of the four clauses
dropped, the three false savings all came back — one at a time, each
found by an assembly that could not close.

**Correction (§13): the fourth came back too.**  `AnnotOk` was recorded
here as the one genuine saving, "no counterpart in a syntactic layer".
That is right about its *binder* clause and wrong about its
*application* clause, and `pairEtaCert` is the assembly that could not
close.  So the score is four out of four, not three: **every clause
dropped on a policy argument was eventually needed.**  The rule still
discriminates — it just discriminates by making you write the consumer,
and the consumer for this one was two hundred lemmas downstream.

## 13. BLOCKED: `pairEtaCert` does not certify its own type arguments

The one obligation of `CheckStepTT` that cannot be discharged as the
checker and the layer now stand.  Everything below is the full stack,
because the conclusion is a request for a decision, not a report of a
missing lemma.

### The obligation

`stuckIrrel`'s first two links are `pairEtaCert a b` and
`pairEtaCert b a`, so `StuckIrrelStepTT` owes

```
pairEtaCertP env fuel d a b = .ok true  →  Deq Δ ⟦a⟧ ⟦b⟧
```

with `a = C pα pβ s₁ s₂` a fully applied pair constructor and `b` stuck.
`pairEtaCert_inv` gives: `b`'s inferred type whnfs to
`PSigma'.{us'} A B`; `Level.isEquivList us us'`; and four verdicts —
`defeq pα A`, `defeq pβ B`, `defeq s₁ (b.1)`, `defeq s₂ (b.2)`.

Congruence turns the four into
`Deq Δ ⟦a⟧ (psigmaMkT u v ⟦A⟧ ⟦B⟧ (pfstT ⟦b⟧) (psndT ⟦b⟧))`, premise-free
(`congrApp` asks for nothing).  What remains is exactly the layer's
structure-η:

```
| psigmaEta {Γ u v A B p} :
    HasType Γ A (.sort u) →
    HasType Γ B (arrow A (.sort v)) →
    HasType Γ p (psigmaT u v A B) →
    HasType Γ .prf (.eqE (psigmaT u v A B) p (psigmaMkT u v A B (pfstT p) (psndT p)))
```

The third premise is available (`InferClaimsTT` at `b`, then
`WhnfClaimsTT` at its type, then `Deq.conv`).  **The first two are
not, and nothing in the checker's run establishes them.**

### Why the premises cannot simply be dropped

They are not decoration.  `psigmaEta_law` (`Setlec/TT/Semantics/Value.lean`)
consumes `hA : A ∈ˢ univ u` and `hB : B ∈ˢ piC A fun _ => univ v` twice
over — once to fold `interp_psigmaT` through `psigmaV_app`, once inside
`psigmaMkV_app` — so §2.4's test ("a premise soundness never consumes")
does **not** condemn them.  This is *not* another §10.2: the rule is
correctly constrained; the certificate is under-specified.

### Why the set-model path does not have this problem

`pairEta_sound` (`Setlec/Model/Core/PairEta.lean`) gets the two
memberships from **`AnnotOk` of the whnf'd type of `b`**:

```
obtain ⟨haCA, haB, vf₁, vB, A₁, B₁, hf₁i, hBi, hpi₁, hvB₁⟩ := haPi
```

`AnnotOk`'s *application* clause carries "the argument is a member of
the function's domain" at every application node.  Applied twice to
`PSigma'.{us'} A B` it yields `vA ∈ˢ univ (ψ u)` and
`vB ∈ˢ pi … vA …` — precisely `psigmaEta`'s two premises.

The bridge dropped `AnnotOk` from all four claim families on the
argument (§ "The four claims") that *a derivation supplies at each
binder what `AnnotOk` was reconstructing*.  That argument is sound for
the **binder** clause and unsound for the **application** clause:
`HasType.app` fixes the argument's type to the domain of the function
type *used in that application*, and a derivation of the whole
application (which is all `InferClaimsTT` returns for the type `tb`)
existentially quantifies that domain away.  This is the same structural
fact as §6's "why the certificates are structural", read in the other
direction: **because the layer will not let you descend into an
application's derivation, the facts about the arguments have to be
*certified where they are used*, and `pairEtaCert` is the one place in
the checker that uses them without certifying them.**

### The certificate is the odd one out

Every sibling in the same chain already certifies its type arguments:

| certificate | what it certifies about its type arguments |
| --- | --- |
| `structUnitCert` | `iotaCerts` on the family's parameter telescope |
| `structEtaCertWith` | `iotaCerts` on the family's telescope, plus `structEtaProjCerts` |
| `.proj` (`inferBody`) | `projParamCert` — landed as task #129 for exactly this reason |
| `pairEtaCert` | **nothing** — two bare `defeq`s against `A` and `B` |

So this is not a general weakness of the certificate discipline; it is
one function that was written before the discipline was settled and
that the set model happened to cover from a different direction.

### The three ways out, and the recommendation

**(A) Certify the pair's telescope in `pairEtaCert` — recommended.**
The pair *is* the native projection entry, and `projParamCert` is the
certificate already written for it: `projEntry_tele_premises`
(`Setlec/TTVerify/ProjStep.lean`, proved) turns a successful
`projParamCert entry us [A, B]` into
`HasType Δ VA (.sort u)` and `HasType Δ VB (arrow VA (.sort v))` —
`psigmaEta`'s two premises, verbatim, with the bridge-side lemma
already in hand.  Cost: one extra certificate call on a two-element
telescope, in a function that already runs four `defeq`s.  Risk:
strictly conservative — extra checks can only turn accepts into
rejects, so the exposure is measurable by re-running the arena and the
e2e battery.  This is a **kernel change** and therefore not the
bridge's to make.

**(B) Reintroduce an `AnnotOk` analogue in the claims.**  A
typing-valued "annotation truthfulness" threaded through
`WhnfClaimsTT` and produced by `InferClaimsTT`.  This is the faithful
transpose of what the model does, it would close the obligation with
no kernel change — and it is a large, invasive change to all four claim
families that buys exactly one clause.  It also re-imports the cost the
bridge was designed to avoid.

**(C) Leave `pairEtaCert` uncertified and carry the obligation.**
Honest but bad: it leaves `CheckStepTT` permanently modulo a named
`Prop`, and the `Prop` is not obviously true — its truth is a
canonicity-strength statement about the layer, not a lemma.

Recommendation: **(A)**, with the `projParamCert` spelling rather than
a fresh `iotaCerts` call, because the conversion lemma already exists
and because it makes the pair's two certificates (projection and η)
consume the same evidence.
