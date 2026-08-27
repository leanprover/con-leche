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

**And the practice has a final form, from the two ways it has been
violated.**  §12.10's instances are clauses this bridge *dropped*
against the set model's field, judging them consumerless; §14.4's
`hheadRec` is quantification this bridge *added* against the same
field, generalising where the model states a closed equality and does
the level bookkeeping at the fire site.  The model's field was right
in both directions.  So:

> **Transpose the model's statement, not your reading of it.**  Where
> the transpose deviates — a clause dropped, a quantifier widened —
> that is a claim about the original, and it needs the same evidence
> any other claim does.

**The family, closed.**  A third member appeared later (§8.6's
factoring rule) and completes it, because it is the limit case of the
first: a lemma with **no possible consumer**.

| what you see at the use sites | what it says |
|---|---|
| a shim | the definition has the wrong **shape** |
| the same bookkeeping repeated | it is missing a **hypothesis** |
| a conjunct destructured to `-` | it was **offered** a hypothesis and declined it |
| no use site can exist | it was **sliced where the code does not slice** |
| a "trivial" lemma that will not go through | the **relation carries more than you thought** |

The third is the second's mirror image and was found the same way
(§14.4, the `hheadRec` narrowing): the inversion `iotaRec_inv` handed
back the fire site's `isEquivList` guard as a conjunct, and the sole
consumer was throwing it away with a `-` — while the invariant it fed
quantified over exactly the levels that conjunct excludes.  Repeated
bookkeeping says the abstraction is *missing* a hypothesis; a
discarded conjunct at the only use site says one was *available* and
the abstraction was stated without it.

The fourth is the sharpest because it is not a matter of degree: a
lemma that is true, compiles, and can never be applied is one that cut
a sequential body at a point the body does not expose.  The first four
are read off the consumers — including, in the fourth case, off their
absence.

The **fifth** is the only one read off the *definition* rather than the
use sites, and it fires earliest of all: before there is a consumer at
all.  Instance (§15, `SameDoms`): the relation looked like an ordinary
congruence, so its reflexivity lemma got written first, by reflex —
and it is **false**.  A non-`∀` type has no domains to agree about, so
`SameDoms T T (x :: xs)` is unprovable; the witness has to come from a
*fitting* (`VTeleTyped.sameDoms`), not from the type alone.  What the
failure was announcing is that the relation is genuinely **partial**:
it is not "these two types are alike" but "this spine fits both", and
the spine is doing work.  (The relation is now `TeleAlign`: the same
partiality, plus **both residuals named**, because a fold has to
continue past the retarget — the statement's telescope does not end
where the type former's does, so "some residual exists" is exactly the
fact it cannot use.  That second correction came from the same source
as the first: asking what the *consumer* would do with the conclusion.)  Writing the plausible version first is what
surfaced it, which makes this tell cheap to trip on purpose — *when a
new relation appears, try its trivial lemmas immediately; the ones
that refuse are describing the relation.*

### The third practice: the checker is telescope-shaped throughout

> **Every telescope-shaped obligation in this bridge decomposes against
> the same walk** — and an obligation that does *not* decompose against
> it is a signal the obligation is stated wrong.

`TeleTyped` (the `Expr` side), `VTeleTyped` (the term side) and
`BetaSpine` (the reduction side) are three inductives with the same
`cons`, and they compose with no glue: `VTeleTyped`'s `cons` hands
`BetaSpine`'s `cons` exactly the `HasType Γ x A` it wants, at exactly
the instantiated domain, in order.  The reason is one fact about the
*object*: the checker's recursors, its iota rules and its certificate
frames are all built by walking the same telescope, so a bridge
relation that walks it too meets the others already aligned.

**Provenance, because that is what distinguishes this from an
inspection-based claim.**  Filed as a *candidate* on the evidence of
two blocks; deliberately held out of this list under the counting
discipline (two instances is a coincidence of coincidences); paired
with a second candidate about the stored rule format and recorded as
**dependent on it**, so that a single adapter would have withdrawn
both; tested at `Nat.rec`, the first block with **two rules and a
field**; confirmed, with the residue named.

**And the residue is named, because a diagnostic needs its
counterexample.**  The `succ` obligation did require rewriting — six
`inst_liftN_absorb` equations, normalising `((liftN 3 M).inst z 2).inst
s 1).inst n` down to `M`.  That is **arithmetic bookkeeping**: de
Bruijn index normalisation of facts that are already correct.  It is
*not* an adapter, which would be a step that **reorders, reshapes, or
supplies something the telescope failed to give**.  A
"no-rewriting-at-all" pass criterion would have failed this test, and
that criterion would have been wrong — so anyone applying the
diagnostic above should know that absorb equations are not the signal.

### A gate note: a warnings check on a cached build is vacuous

A warning escaped to `master` (`DeclBasis.lean:881`, an unused binder)
while every landing report claimed a warning-free build.  The mechanism
is worth writing down because it will recur:

* **Lean emits a file's warnings only when it *compiles* that file.**
  An incremental `lake build` that finds everything cached prints a
  summary and nothing else — so a warnings check run against a cached
  build is not a weak check, it is **no check at all**.
* The warning was therefore emitted exactly *once*, on the build right
  after the edit that introduced it, into a command filtered with
  `grep -E "^error"`.  Every later build was cached, and the
  landing-time gate used `| tail -1`, which shows only the summary
  line.

Two independent holes, and either alone would have caught it — which is
the usual shape of an escape.  The gate for a landing that touches
`Setlec/TTVerify/*` is therefore:

```
rm -f .lake/build/lib/lean/Setlec/TTVerify/*.olean
lake build 2>&1 | grep -E "^(error|warning)"      # must print nothing
```

The general rule: **a check whose input is produced by a cache must
first invalidate that cache, or it is measuring the cache.**  The same
reasoning applies to any "we ran it and saw nothing" gate.

**It caught a defect on its first run** — an unused parameter in the
increment that introduced the corrected procedure, by exactly the
mechanism diagnosed above.  A process fix that finds something the first
time it is used is as good a validation as a process fix gets.

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
replaced, weakened or deleted — and since the 2026-08-26 ruling that
coexistence is **permanent and asymmetric**: the set model proves the
shipped checker consistent, this path covers the certified
configuration as a conditional theorem.  §4's "end state" subsection
states the division of labour and why the alternative was refuted
rather than declined.

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
| `WhnfCoreClaimsTT` | **closed** |
| `DefEqClaimsTT` | **closed** |

**`CheckStepTT` is proved** (`checkStepTT`, `Setlec/TTVerify/MajorStep.lean`),
with no outstanding hypothesis, and `checkClaimsTT` gives the four claim
families at every fuel.  Task #130 closed the last one; the edit was
exactly the predicted one — replace the parameter with
`pairEtaCert_stepTT` and delete it.

The three `WhnfCoreClaimsTT` chain links closed with no surprises, and
two of them are §2's identity a third time: `litMajorToCtor` and
`projLitToCtor` expand a literal to its constructor form, and both
expansions are `denote`-**transparent** (`denote_natLitToConstructor`,
`denote_strLitToConstructor`), so the accumulated equation does not
grow across them.  `majorToCtor` is the one with content, and its two
obligations were both discharged by *the checker's own guards*
(§8.4 at its cleanest): the fabrication's frame conditions are exactly
the three Booleans of the scope guard `majorToCtor` already runs
(`wscopedB`, `looseBVarsBounded`, `fvarLeaves ⊆ major`'s), and the
fabrication's *denotation* is exactly what the synthetic-spine
`iotaCerts` of task #71 produces once `certs_typed` transposes it.
Neither guard was added for the bridge.

### `CheckDeclTT`, in progress

The dispatch is proved (`checkDeclTT_of`, `Setlec/TTVerify/DeclStep.lean`):
six obligations, one per constructor of `Declaration`, each stated as
`checkDecl` restricted to that shape — §8.6's permitted *input-space*
restriction, not a body slice.

**The three value-carrying kinds are done**, all through one shared
install:

| case | status |
| --- | --- |
| `DeclThmTT` | **proved** |
| `DeclOpaqueTT` | **proved** (`declOpaqueTT_closed`) |
| `DeclDefnTT` | **proved** (`declDefnTT_closed`; both `Nat` pins discharged) |
| `DeclAxiomTT` | **proved** (`declAxiomTT_closed`) |
| `DeclBasisTT`, `DeclIndTT` | open — **decomposed in §14** |

**§11's `Eq` law landed** (`EnvTT.eq_law`), released by its consumers
exactly as §11 said it would be: all three standard-axiom keys have to
turn a spine over the stored `Eq` into the layer's `eqE` former, so the
law's first three consumers arrived together.  With it came the
infrastructure they share — `denote_erasedEq` and `denote_matchesPin`
(`Setlec/TTVerify/Inst.lean`), the transpose of `interp_erasedEq`.

That pair is worth its own §8.4 line.  `ConstantVal.matchesPin`
compares a stored type to a pinned one **up to binder names**, and
`denote` reads a binder's name only to build the `fvar` it opens with —
whose denotation is a de Bruijn index.  **The pin's tolerance and the
denotation's blindness are the same set of syntax.**  Nobody arranged
that; it is why a `matchesPin` hit is usable by the bridge at all, and
it is why every inhabitation key gets to compute on the *pin* rather
than on whatever the stream happened to send.

`extendValueTT` is the transpose of the set model's `extend_model`, and
the three kinds differ only in which `ConstantInfo` they hand it — which
is also which of `defn_eq` / `thm_ok` is the non-vacuous field.  `value_key`
is the whole content: `InferClaimsTT` at the checked value, then
`DefEqClaimsTT` at the checker's own `vtype ≡ type` verdict.  **The
per-declaration step is the per-expression claims applied once each**,
which is why it could be left until stage 2's end.

Both obligations sat at named checker functions (`certifyNatEqs`,
`checkDivModPin`), per §8.6, and **both are now discharged**; their
shared content is `denote_substConst0`
(`Setlec/TTVerify/SubstConst.lean`).

Both pins certify in the **pre-insertion** environment with the
operation's self-references replaced by its stored value — because
certifying after insertion would let the operation's own literal fast
path discharge its all-literal equations vacuously.  So the bridge has
to move a `Deq` across `Expr.substConst0`, and it does so for free:
`cvalAt` sends the installed name to the *value's denotation*, which is
exactly what `substConst0` writes in its place.  **The install's choice
of valuation and the checker's choice of substitution are the same
choice**, made for unrelated reasons — one to satisfy `defn_eq`, one to
defeat a vacuous fast path.

The lemma is restricted to the fragment `substConst0` is faithful on
(`sort`, `const`, `fvar`, `app`), which is not a limitation dodged:
`substConst0` is *shallow* by design and `natOpEquations` are spines
over constants and two free variables with no binder anywhere.  Note that both are
*pin* checks: they change no environment and exist only to record facts
the reduction rules will consume, so their transposes are pure content
with no install bookkeeping.

**`NatOpPinTT` is discharged** (`Setlec/TTVerify/NatOpPin.lean`).  Its
content is one induction — `natFrag_subst_facts` — that produces, in a
single pass over an equation side, everything `DefEqClaimsTT` asks for:
the three frame conditions, the `CtxOk` correspondence in `[Nat, Nat]`,
and the denotation.  Then `denote_substConst0` moves the resulting
`Deq` across the install.

A third §8.4 alignment, and the most literal one yet.  The fragment the
bridge must denote is: `Nat.zero`, `Nat.succ`, the operation, its
dependency operations, and (for `beq`/`ble`) the two `Bool`
constructors.  That is, name for name, what `natOpGuard` checks is
stored at empty level parameters — `natLitSupported` for the first two,
`natOpDeps` for the middle, the `beq`/`ble` branch for the last.

> **`natOpDeps` was written so the *checker* could certify the
> recurrences.  It lists precisely the constants the *bridge* must be
> able to denote.**

The guard's dependency list and the bridge's denotation obligation are
the same list, and neither was written with the other in view.  One
wrinkle is worth recording because it is the kind of thing that
generalises: `natOpDeps c` contains `c` itself, so the transfer of
guard facts from the extended environment down to `env` needs an
`n ≠ c` side condition at each use — the operation's own entry is the
one dependency that is *not* available below.  The fragment lemma takes
that side condition as a hypothesis rather than proving freshness
internally, which is why it stays a statement about `env` alone.

**`DivModPinTT` is discharged** (`Setlec/TTVerify/DivModPin.lean`), and
with it `DeclDefnTT`.  Four things from it are worth keeping.

> **The inert type slot pays for the guards.**  A clause hands the
> bridge `Deq Δ (ble y x) true`, but the certificate wants an
> *inhabitant* of the stored `Eq` spine.  `Deq.toHasType` re-slots a
> derivation at **any** type, so the guard converts with no
> unique-typing argument anywhere: pick the slot the law wants.

Derivational inertness of `eqE`'s type argument entered this project as
a curiosity (§5, "the slot is never checked"), became a caution (§12's
contract discussion, where it is why the choice between three contracts
is cheap rather than consequential), and is now doing load-bearing
work for the third time.  **Curiosity → trap-warning → tool** is the
whole trajectory, and it is worth naming because the third stage is not
predictable from the first two: a property that makes a design *hard to
get wrong* turned out to also make a proof *possible*.

**The extra binders cost nothing** (`Deq.close4`).  A certificate
checked under two `ble`-guard hypotheses closes at exactly `close2`'s
instantiation: each hypothesis type and the equation are lifted over
the binders below them, so every instantiation the `app` rule performs
at a proof binder meets a lift and is absorbed.  There is deliberately
no three-binder variant — the checker runs *every* certificate at depth
`4` whatever its hypothesis count, and `CtxOk` ties the context length
to the depth, so a one-hypothesis frame is a four-entry context with an
entry no leaf mentions; give it the used hypothesis's type and inhabit
it with the same proof.

**One place the object-level route does not reach.**  `lam`/`app` moves
a `Deq` from the frame to the caller's arguments for free, but the same
trick cannot move a *typing*: it would put the subject in a redex,
which no rule concludes (F1, §6).  So `HasType.close2` is the one use
of `HasType.instN` in this whole file — exactly the residue
`Setlec/TTVerify/HasTypeSubst.lean` says the substitution stack is
for.

**The §8.4 alignment repeats, twice in one file.**  `natOpDeps` is the
list of constants the *checker* needs to certify the recurrences; it is
also, name for name, the list the *bridge* must denote and type — and
`divModEnvGuard` pins exactly `natOpDeps c` plus the two `Nat`
constructors, the two `Bool` constructors and the pinned equality,
which is exactly what `DMBase` carries.  Neither list was written with
the other in view.  The one wrinkle worth a rule: `natOpDeps c`
contains `c` itself, so every transfer of a guard fact from the
extended environment down to `env` needs an `n ≠ c` side condition —
**the operation's own entry is the one dependency not available
below**, and the lemmas take that as a hypothesis rather than proving
freshness internally, which keeps them statements about `env` alone.

**`DeclAxiomTT`'s guard chain is proved** (`Setlec/TTVerify/DeclAxiom.lean`),
modulo one inhabitation key per accepting guard — `StdAxiomKeyTT`,
`TrustCompilerKeyTT`, `OfReduceKeyTT`, each at a named guard function
per §8.6.  Two things about that case are worth keeping:

* **The tolerated-axiom branch is one line.**  A skipped axiom installs
  nothing, so the environment the invariant talks about never moves and
  the model we started with is the model we return.  The
  skip-and-continue design (`sorryAx`, user ruling) therefore pays a
  *zero* verification tax — a design chosen for stream-sharing reasons
  turns out to cost the bridge nothing at all.
* **`PropextKeyTT` is discharged, and §8.4's prediction is
  CONFIRMED.**  The prediction, made before any of the keys were
  written, was: *the witness is the layer's constant under an `Iff.rec`
  elimination, needing the recursor's **typing** and never its iota
  rule.*  Both halves hold, and the second is checkable by inspection —
  `Setlec/TTVerify/StdAxiomKey.lean` never mentions `rec_rules`.

  That half is not cosmetic.  Had the iota rule been needed, the axiom
  case would depend on `EnvTT.rec_rules` **at a modeled family**, which
  is established by the still-open `DeclIndTT` — and `DeclAxiomTT`
  could not have been closed before the inductive install.

  > **The prediction bought an ordering, not just a shape.**

  That is the strongest form a prediction can take here, and it is why
  the ceremony is worth keeping: an ordering constraint that does *not*
  exist is invisible until something depends on it, and a shape
  prediction that happens to carry scheduling information tells you the
  dependency is absent *before* you schedule around it.  `DeclAxiomTT`
  closed while `DeclIndTT` had not been started, which is the
  observable consequence.

  The elimination is *unavoidable*, and it is worth saying why in one
  line, because it is the first key where reconciliation alone did not
  suffice: `Iff a b` is an ordinary modeled inductive, opaque to the
  bridge, and **nothing in the layer turns an inhabitant of an opaque
  family into its fields except that family's own recursor.**  Which is
  precisely why `stdAxiomOk` pins `Iff`, `Iff.intro` *and* `Iff.rec`
  rather than `Iff` alone — §8.4 again, at the last place it can apply.

  **`ChoiceKeyTT` is discharged too, and it was the cheapest key** — as
  predicted, and for a reason worth recording because it is a property
  of the *pin* rather than of the proof: `Nonempty.rec`'s motive sort is
  written into the pin as `Prop`, where `Iff.rec.{u_1,u}` carries it as
  a level parameter that has to be driven to `0` by a bespoke
  assignment (`atZero`).  One field instead of two is the small saving;
  **no level gymnastics at all** is the real one.  A pin that fixes a
  level is easier to consume than a pin that quantifies one, even when
  the quantified pin is more general.

  So the inhabitation-key story is complete in three shapes:
  `trustCompiler`, where the pin fixes the type on the nose;
  `ofReduce*`, where a certificate already proved the equation; and
  `propext`, where an elimination is required.  Only the third needed
  anything the first two did not, and what it needed was a *typing*.
* **`OfReduceKeyTT` is discharged** (`Setlec/TTVerify/OfReduceKey.lean`),
  and it is the reconciliation shape at its purest: **no layer constant
  is used at all**.  The witness is `λ a b h. prf` — three lambdas and
  the layer's canonical inhabitant of any `eqE` — because *the
  hypothesis is the conclusion*: the reduce opaque was certified at its
  own install to be the identity on its element type
  (`ReduceOpsTT` ← `ReducePinTT`), so `reduce a ≡ a` and the equation
  `h` carries is already the one the conclusion wants.  Everything
  between is conversion: `denote_matchesPin` for the spelling,
  `EnvTT.eq_law` for spine-to-former, `EnvTT.reduce_ops` for the
  identity.  Two obligations discharged by one certificate the checker
  ran for a different reason is §8.4 compounding.
* **`TrustCompilerKeyTT` is discharged**, and it shows the shape the
  other two follow.  The pin fixes the axiom's type to `.const True []`
  *on the nose* — `eraseNames` is the identity on a bare constant — so
  the witness is the stored `True.intro`'s valuation and the derivation
  is `cval_hasType` at the pinned type.  **No layer constant is
  involved**: `True` is an ordinary modeled family, and being modeled is
  enough, because the pin puts the *constructor* at exactly the type the
  axiom wants.  The lesson generalises to the remaining two: an
  inhabitation key is not an inhabitation *argument*, it is a
  reconciliation between two spellings of one type.
* **`propext` and `Classical.choice` need no inhabitation argument.**
  Both are already `BConst`s with `bval` and soundness
  (`Setlec/TT/Const.lean`, `Setlec/TT/Semantics/ConstOk.lean`), so
  `HasType.const` types them.  What the keys owe is a **shape
  reconciliation** — the layer's `∀ A B : Prop, (A → B) → (B → A) → A = B`
  against the checker's pinned `∀ a b : Prop, Iff a b → Eq Prop a b`,
  with `Iff` an opaque modeled inductive.  And that is precisely what
  `stdAxiomOk` pins `Iff`/`Iff.intro`/`Iff.rec` for: the witness is the
  layer's constant under an `Iff.rec` elimination, needing only the
  recursor's *typing*, never its iota rule.  §8.4 at the last place it
  can apply.

**`ReducePinTT` is discharged** (`Setlec/TTVerify/ReducePin.lean`), and
it is worth a sentence because of *how cheap it turned out to be*.  The
checker certifies the compiler-trust identity as an **open** equation at
depth `1` — `isDefEq env 1 (valA x) x` with `x` the single opened
variable at index `0` — while `ReduceOpsTT` wants it closed, at an
arbitrary context and an arbitrary derivably-typed argument.  That
transport is two moves and no lifting algebra:

| move | lemma |
| --- | --- |
| `[E]` becomes `E :: Δ` | `HasType.weakenTail` — because `[E] ++ Δ` *is* `E :: Δ` |
| the opened variable becomes the argument | `HasType.instantiate` |

> **A certificate stated at depth `d` with its variable at index `0` is
> exactly the shape the substitution lemma consumes.**

A certificate written instead over a fresh *constant*, or at depth `2`
with the variable buried, would have cost a context-surgery lemma.
Nothing in the checker was arranged for this — the depth-`1` spelling is
just the natural way to write an open certificate — but it is another
instance of the §8.4 pattern, and worth naming so that the next
certificate is written the same way on purpose.

One mechanical note worth recording, because it will recur: **a `match`
written in a lemma's *statement* is a different auxiliary constant from
the one in the checker's body**, so a tail cannot be factored out by
restating its `do`-block shape.  The divergence is invisible (the two
print identically up to a binder name) and the error reads as a type
mismatch between two syntactically equal expressions.  Factor at a
`cases` boundary instead, or duplicate the walk.

Two more §12.10 clauses came back while writing it, and both were
*over-strong hypotheses* rather than missing facts:

* **`LitAgree` and `Installs`' two level-parameter clauses are now
  conditional on the guard.**  The unconditional form was not merely
  inconvenient, it was **false**: nothing in `checkConstantVal` forbids
  a `def` named `List.nil`, and the string-support names are pinned,
  not reserved.  Under the guard every one of the seven is *stored*,
  hence not the fresh name — so `Installs.of_fresh` now costs a caller
  exactly one hypothesis, which is what an install lemma should cost.
* **`EnvTT` gained `rec_ctors`.**  `RecCtorsStoredT` was dropped as
  "syntactic, no consumer", and `EnvTT.cons` promptly took it as a
  *hypothesis* — a consumer found and then billed to the caller rather
  than to the invariant.  A `theorem` install has no recursors of its
  own and cannot prove anything about the ones already stored, so the
  fact belongs to the environment.

Discharged inside `WhnfCoreClaimsTT`: `LitMajorToCtorStepTT`,
`ProjLitToCtorStepTT`, `MajorToCtorStepTT` — hence `IotaStepTT` and
`ProjStepTT`, hence the quarter.

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

### The end state: two conditionalities, documented together

**USER RULING, 2026-08-26 — this is the final architecture, and the
framing this document uses from here on.**

> "Yes, finish the TT bridge as well, maybe we'll need it.  But this
> means we also keep the direct checker→set model bridge alive and it
> is what proves the real checker (with fast `infer_only`) consistent."

The original ambition — *checker verification retargets onto this
layer, and the set model becomes the layer's own semantics* — is dead
for the shipped configuration.  It died **by refutation, not by
preference**, and the two refutations are worth keeping because both
were reached by trying:

* **Execution preservation: BLOCKED.**  Carrying the checker's verdicts
  onto the layer through a preservation argument needs transitivity and
  stability of the *executable* definitional equality at the beta
  tentpole.  The arena's own good/undecidability tests contradict
  exactly that, and lean4lean's corresponding metatheory is `sorry`ed
  behind a ~13 000-line graveyard of failed attempts.  This is not a
  gap waiting for effort.
* **The `DeqC` middle layer: REJECTED.**  A conversion relation sitting
  between the two would have bought the preservation step at the price
  of syntactic restrictions on the rules — against the settled
  core-generic-over-env value (`Setlec/Model/DESIGN.md`, "no basis
  special-casing in core rules").

So the three parts of the final architecture, stated as they should be
quoted:

1. **The set model is the consistency proof of the real checker in its
   *default* configuration** — the shipped binary with direct install,
   `SETLEC_INFER_ONLY` **off**.  Nothing in task #119 weakens, replaces
   or deletes any of it, and a reader wanting "is the thing we ship
   consistent?" is asking the set model, not this file.

   **CORRECTED, 2026-08-27.**  This entry used to promise that the set
   model would cover the fast `infer_only` path too, "via the #109
   `pt`-freshness / domain-determination route now in progress".  That
   route was **refuted by the whole-stream census** (1–4 % capture even
   with a free guard; top-level `DESIGN.md`, the census section at
   commit `3078208`), and task #134 landed `infer_only` as a
   *supported but unverified* operating mode: flag-off is verified,
   flag-on carries **reference-kernel parity** rather than a soundness
   proof.  So the coverage claim is now explicitly flag-off, and the
   promise is withdrawn rather than left standing as pending work.
2. **The TT bridge covers the *certified* configuration** —
   certificates on (`SETLEC_INFER_ONLY` off) and
   `directStructsEnabled = false` — as a **conditional theorem**.
   Both are named `Prop`s or named build constants, never hidden side
   conditions.

   **There are now three conditionalities in this project, not two**,
   and they are of two different kinds.  `directStructs` and the
   certificate flag are conditions *this* file's theorems carry.
   `SETLEC_INFER_ONLY` is a third, and it is the one neither
   verification path covers — the set model's claim stops at flag-off
   and the bridge's does too.  A reader checking which claim a verdict
   carries has to read the invocation, which is why #134 made the two
   diagnostic flags mutually exclusive on the command line.
3. **The layer's unconditional returns** are not conditional on
   anything: `Setlec/TT/*`'s own absolute consistency, its two-lemma
   metatheory, and the design-instrumentation record this document is
   — the call-site tell, the certificate tax, the §8.4 alignments, the
   over/under-hypothesis rules.  Those were the returns whether or not
   the retargeting ever happened, and they are why the bridge is worth
   finishing.

What follows is the *first* of the two conditionalities in detail; the
second is the certificate configuration, and the accounting for it is
§6's — the tax measurement there is the same flag read from the
performance side.

#### The direct-install hypothesis, and what it costs

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

Under the 2026-08-26 ruling this is no longer a temporary state to be
exited but the settled division of labour, and the reason it is
acceptable is the second bullet below rather than the first.

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

**Exit condition — for this flag only.**  The TT route covers the
shipped default's *structures* once one of two things happens: the
layer supports directly installed structures (their tower encoding
denotes, as `Setlec/Model/DirectTower.lean` already interprets it), or
direct install is retired — the standing plan the moment the class
earns `eta`/`unitlike` and `lean-inductive-models` stops emitting
artifacts for it (top-level `DESIGN.md`, "Task #82 is complete").
Clearing it would still leave the certificate flag, so even then:
**quoting a TT consistency theorem as a statement about the shipped
binary is a category error.**  The statement about the shipped binary
is the set model's.

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
   so the app-argument certificate — 98.6 % of the tax, on the measure
   amended at §6.1 — is permanent
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
alias for `SETLEC_NO_PROOF_CERTS`.

> **AMENDED, 2026-08-27 (task #134) — the 98.6 % share is right, the
> *tax* it is 98.6 % of is not.**  `--yolo` drops the per-argument
> application check at **every** invocation, the driver's front door
> included — and the front-door check is one the reference kernels
> perform too (`check(e)` at `infer_only = false`).  So part of what
> the mask attributed to *certification* is ordinary checking that any
> kernel does, i.e. engineering gap.  Measured against #134's
> infer-only mode, which keeps the front door and drops only the
> internal re-checks, the honest certified-mode tax is **~1.9× on
> `Std.Time`**, not the ~42× the old framing implied — roughly half the
> old number was front-door work.  See top-level `DESIGN.md`, "The
> infer-only mode: SETLEC_INFER_ONLY (task #134)", for the
> decomposition.
>
> **What this does *not* change is the argument this section makes.**
> The re-check is still the dominant certificate, still exists only
> because `AnnotOk` is a conclusion rather than a carried hypothesis,
> and is still the thing a typing judgment would obviate at the
> *internal* sites.  The correction is to the size of the prize, not to
> where it comes from — and §6's "the tax is one call" reading survives
> with a smaller number attached.

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
| app-argument re-check (`inferSpineI`) | yes — the 98.6 % (see §6.1's amendment) | **no** | *established* (four routes closed) |
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

The measurement above (as amended — the *share* stands, the tax it is a
share of is smaller) says the app-argument re-check is 98.6 % of the
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
certificate is the one call that costs 98.6 % of the tax: it is doing
the one
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

**Why the count keeps rising** (eight instances at the time of writing
— the guard congruences, `DivModTT`'s transport, `denote_params_ext`'s
literals, `denote_instLevels`'s literals, `strLitSupported`'s ten
pinned types, #129's projection entry, `natOpDeps` at the recurrence
pin, and `divModEnvGuard`'s list at the div/mod pin).  It has stopped
being a pattern and become a property of the design, and the property
is one sentence:

> **The pins exist so the *checker* can compare against known shapes,
> and the same pins are why the *bridge* can compute against them.**

**The alignment is now measurable, not just anecdotal.**  The div/mod
pin's nine per-operation assemblies were written against one shared
pair of drivers, from the guard's own dependency lists — and **seven of
the nine compiled on first write**.  The two that did not (`Nat.div`,
`Nat.mod`) failed for a reason unrelated to the alignment:
`DivModClausesTT`'s own internal `if c = natDivName` survives into the
goal and has to be reduced.

That number is a better metric of design coherence than any single
alignment anecdote.  A first-write success rate under a shared driver
measures whether the guard's list, the denotation's needs and the
law's shape actually coincide — if they only *nearly* coincided, the
per-operation work would be where the discrepancies surfaced, and it
is exactly where they did not.

**Two kinds of instance, and a reader should be told which.**  (The
first kind's list keeps growing, and at this count the growth is no
longer the interesting part: **both artifacts answer to the same
object**, so agreement is what should be expected and a *dis*agreement
would be the finding.  The entries are kept because each one names
*which* piece of the object forced it, not because another coincidence
is surprising.)  Every
instance above is of the *first* kind; the basis install produced the
first of the second, and they are different evidence:

* **Undesigned coincidence** — two artifacts, each faithful to the same
  object, agreeing without either author knowing about the other.
  `natOpDeps`, the guard congruences, `strLitSupported`'s pinned types,
  #129's projection entry.  The evidence is about the *object*: the
  agreement is forced because both sides are reading the same thing.
* **Deliberate forward provision** — a clause written for a consumer
  that did not exist yet, which turns out to be correctly sized when
  the consumer arrives.  `EtaFamilyStored`'s first conjunct
  (`Setlec/Verify/EnvGuards.lean`) is documented as existing "to keep
  the basis installs' head obligations vacuous by computation", and
  `extendBasisTT` is the install that finally collected on it.  The
  evidence is about the *author*: someone predicted a shape and got it
  right.

Three more from the basis blocks:

* **`Nat`'s constructor levels — undesigned.**  `Nat.zero` and
  `Nat.succ` bind no level parameters, so a fired rule's `usj` is
  forced to `[]` and the level mismatch that `PUnit` needed `punitEta`
  for is *unrepresentable*.  Nobody made `Nat` level-monomorphic to
  help this proof; Lean's `Nat` simply has no universe parameter.
* **`Eq`'s closure — a forward provision with unusual provenance.**
  `HasType.proofIrrel`'s two sides need not inhabit the *same* `Prop`.
  That relaxation (#127) was adopted on doctrinal grounds — soundness
  reads `mem_univ_zero` of each side independently, and §2.4 forbids a
  premise soundness never consumes — and it absorbs a level mismatch
  **nobody had in view when it was made**.

  That last one is the doctrine's strongest possible defence: §2.4 is
  not aesthetics, it is *preemptive generality*.
* **The projection entry's type — undesigned, at `PSigma'`.**  A pinned
  projection's stored type and the layer's projection *rule* agree
  binder for binder: `pairSndTyA`'s body is literally `β (t.0)`, which
  is `HasType.projSnd`'s conclusion `.app B (pfstT p)` at the frame's
  own variables.  So `pairProjValT_typed` is the rule applied once,
  under three `lam`s, for both projections.  The preprocessor writes
  the type; the layer states the rule; neither was written with the
  other in view.
* **The stored rule format — undesigned, CONFIRMED at `Nat`.**  A
  recursor's stored rule right-hand side is **the eliminator's own
  telescope re-abstracted**, so its binders are the type's prefix
  followed by the constructor's fields.  The preprocessor generates
  rules that way for its own reasons; the bridge collects on it because
  `hheadRec`'s telescope premises then arrive in exactly the order the
  reduction consumes them.  Filed unproved at `Eq` (whose rule has no
  fields, and so proved nothing), tested at `Nat.rec` — two rules, one
  with a field — and confirmed.  A rule weakened
  because a premise could not be justified paid out on a problem
  discovered afterwards, which is precisely the return a "no unused
  premises" rule is supposed to earn and almost never gets to
  demonstrate.

Both are worth having and neither substitutes for the other.  A run of
coincidences says the design is coherent; a forward provision that
fits says a specific prediction held.  Conflating them would let a
lucky guess borrow the authority of a structural fact — so each
instance in the list above is of the first kind unless it says
otherwise.

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

### CONFIRMED at the install, with a reason nobody priced

The ruling above chose "fired law" over "pinned valuation equation" by
analogy with `rec_rules` and `caps_ok`.  The install
(`Setlec/TTVerify/DeclBasis.lean`) shows the reason that actually
matters, and it is not analogy:

> **The law gets used in both directions inside a single block.**
> `Eq`'s own typing reads it forwards (spine ⇒ former); `Eq.refl`'s
> reads it *backwards*, `conv`-ing `HasType.refl`'s `eqE` into the
> spine the pinned type demands; and `Eq.rec`'s reads it forwards again,
> to recover `a ≡ b` from its hypothesis.

A valuation *equation* would have given only one direction — it fixes
what the constant **is**, and every consumer would then have to unfold
it. A `Deq`-valued law is symmetric by construction (`Deq.symm`), so
the reverse direction costs nothing.  **Bidirectionality is the reason
to prefer laws over equations**, and it was discovered at the first
consumer that needed the reverse, not at the ruling.

**Which came first matters, so record it.**  The ruling was made *by
analogy* — "matching `rec_rules` and `caps_ok`" — and the analogy is
not an argument: it would not have survived a challenge before the
install existed, because nothing then distinguished a law from an
equation at the sites that were written.  So this is a decision that
was **right before it was justified**, and the justification arrived
from a direction nobody was looking in.  Analogy is a decent prior and
a bad defence; the honest form of the record is to say the prior held
and to name the reason that replaced it.

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

## 13. CLOSED (task #130): `pairEtaCert` certifies its own type arguments

**Resolved.**  Requested here, granted, implemented as task #130
(`DESIGN.md`, "`pairEtaCert` certifies its own type arguments"), and
discharged by `pairEtaCert_stepTT` (`Setlec/TTVerify/PairEtaStep.lean`).
The analysis is kept in full because it is the record of *why* a
checker change was the right repair, and because §13.5 below
generalises one of the implementer's decisions into a standing rule.

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

### 13.4 What landed, and the one thing that surprised the bridge

(A), verbatim: `pairEtaCert` now ends with
`projParamCert entry us' [A, B]`, and `pairEtaCert_inv` gained the two
conjuncts `env.findProj? c' 0 = some entry` and the certificate's
verdict.  The bridge side is the shape the *other three* certificates
in `stuckIrrel` already had, and `projEntry_tele_premises` — written
for #129's `.proj` clause — was reused **unchanged**.

Two implementer decisions were better than what the request asked for:

* **The certificate runs at `us'`, the type's levels, not `us`, the
  constructor's.**  `A` and `B` are `PSigma'.{us'}`'s arguments and
  `psigmaEta` names its premises at the levels of `p`'s type, so
  instantiating the entry at `us'` lands them where the rule wants
  them.  The bridge therefore needs **no `isEquiv` transport** on the
  premises — the `isEquivList us us'` verdict is used only for the
  constructor *head*, where it was already needed.  A request that had
  specified `us` would have cost a level-transport lemma for nothing.
* **Failure is `pure false` and the call sits last.**  Generalised
  below.

**One thing the request did not anticipate.**  `ProjOkT` identifies a
stored entry as one of the two pinned ones only when
`entry.native = true`, and `pairEtaCert` — unlike `inferBody`'s `.proj`
clause — never reads `native`.  So the bridge could not get
`entry = pairFstEntry ∨ entry = pairSndEntry` from the invariant as it
stood.  The fix was on the bridge side and is §12.10 yet again:
`ProjOkT` gained a second clause, *the projection-table entries at the
pinned pair are native*, which is true because `psigmaName` is reserved
so no modeled block can install a template entry under it.  Recorded
because it is the same lesson in a new place: **an invariant guarded by
a condition the consumer does not check is not available to that
consumer**, and the guard has to be discharged by the environment, not
by the call site.

### 13.5 STANDING RULE: a certificate's failure mode follows its position

The implementer's second deviation, hoisted out of #130 because a
future certificate author will not find it there.

> **A certificate on a *checking* path throws; a certificate in a
> *rescue cascade* returns `false`.**

`inferBody`'s `.proj` clause (#129) is on a checking path: reaching it
means the input claims to be a projection, and a failed parameter
certificate means the input is bad, so `.invalid` is right and the
error message is informative.  `pairEtaCert` is one attempt in
`stuckIrrel`'s cascade — tried in *both* argument orders, then four
more certificates, then proof irrelevance.  Throwing there would reject
inputs that the reverse direction or a later certificate still accepts:
the failure is not the input's, it is this attempt's.

Two corollaries, both used in #130:

* **Position follows the same rule.**  A soft-failing certificate added
  to a cascade should go **last**, after the checks that were already
  there.  The verdict is identical either way, but running it last
  means it only fires on rescues that would otherwise have succeeded,
  and it leaves every existing call's error behaviour untouched — so
  the change cannot turn an accept into a *crash*, only into a
  rejection that the cascade then tries to rescue elsewhere.
* **The bridge cannot tell the difference and must not try.**  Both
  spellings give the bridge the same hypothesis (`… = .ok true`), so
  this rule is entirely about the checker's verdict behaviour on
  *inputs the bridge never sees*.  That is precisely why it belongs in
  a written rule rather than in a proof: nothing in the verification
  would have caught the wrong choice.

## 14. SCOUTED: the two block installs, decomposed before grinding

`DeclIndTT` is the tentpole of `CheckDeclTT` — the set model spends
~8 400 lines on the semantic core and ~9 300 more on plumbing — so it
was scouted before any of it was attempted, on the iota precedent
(§0: measure the *function you invert*, not the statement you
conclude).  What the scout found changes the estimate by a lot, in
both directions.

### 14.1 The model's three tiers, and which of them the bridge inherits

| tier | model files | lines | character |
| --- | --- | --- | --- |
| A. checker inversion + environment plumbing | `Model/Extend/*` | 9 311 | **~5 % semantic** |
| B. the fold-fact engines | `IndInstall`, `ProjInstall`, `EtaInstall` | 8 414 | model-theoretic core |
| C. the pinned basis, computed | `Model/Basis/**` | 13 485 | maximally set-specific |

Tier A is startlingly model-free: `Extend/Decl.lean` has **6 semantic
lines out of 1 024**, `Extend/Iota.lean` **2 out of 1 394**.  Every
`check*_inv` and every spec `Prop` (`PlainChecked`, `NestedChecked`,
`RuleChecked`, `EtaPins`, `ProjPhaseInv`) is over `Env`/`Expr` with no
`V` at all.

> **The single most useful number in the scout's report is 2/1394.**
> It says the install's *bookkeeping* is not model-theoretic and was
> never model-theoretic — it is the seventh and largest member of the
> misfiled class named at `EtaFamilyStoredT`, and it is the class's
> strongest case for relocation to `Setlec/Verify/*`.

The bridge cannot import `Setlec/Model/*` (both paths must stand
alone), so today those inversions would have to be duplicated —
9 300 lines of duplication is not a "ten-line restatement" and would be
absurd.  **This is the point at which the relocation stops being
deferrable**, and it is recorded here as the trigger rather than as a
preference: `DeclIndTT` should not begin until the tier-A inversions
live somewhere both paths can import.

> **GATE DISCHARGED (2026-08-27).**  The relocation has happened:
> `Setlec/Verify/Extend/` holds `Decl`, `Ind`, `Inversions`, `Iota`,
> `Modeled`, `Proj`, `Recs`, `Sibs` and `Transport` — **3 934 lines,
> `V`-free** (two files mention `V` once each, in prose) — and the
> bridge already imports from it (`Setlec/TTVerify/DeclValue.lean`
> imports `Setlec.Verify.Extend.Inversions`).  `Setlec/Model/Extend/`
> keeps the 5 591 lines that genuinely carry `V`.  So `EtaPins`
> (`Setlec/Verify/Extend/Iota.lean:917`) and its siblings are
> importable today and `DeclIndTT` is unblocked.  The trigger recorded
> above fired and was acted on, which is the whole point of writing a
> trigger down rather than a preference.

### 14.2 Which fields each engine is actually for

The scout's table, condensed to what the bridge owes:

| model install | `EnvModel` field | bridge counterpart |
| --- | --- | --- |
| `IndInstall.lean` (5 290) | `rec_rules` **only** | `RecRulesTT` head clause |
| `ProjInstall.lean` (2 038) | `rec_rules` **only** (projection fns are stored as degenerate recursors) | `RecRulesTT` head clause |
| `EtaInstall.lean` (1 086) | `caps_ok` **only** | `EtaLawTT` / `UnitLawTT` head clauses |
| `Basis/*/Install.lean` | `mem_type`, `annot_ok`, `val`, `ind_ok` | `has_type`, **—**, `cval`, `basis_pinned` |
| `Basis/*/{Iota,RuleOk}.lean` | `rec_rules` | `RecRulesTT` |

Two entries in that last column are the whole planning story.

* **`annot_ok` has no bridge counterpart at all.**  Roughly a third of
  tier C is `annotOk_<c>_type` / `annotOk_<r>_rhs` families, and the
  bridge dropped `AnnotOk` from every claim.  §13 established that the
  drop was not free — but it costs the bridge *one* clause
  (`pairEtaCert`, now repaired in the checker), against ~4 000 lines it
  does not have to write here.  **That is the trade finally priced.**
* **`proj_ok` is vacuous on the `.indDecl` path.**  Modeled blocks
  install only `native = false` template entries, and `checkProjFn`
  installs a *degenerate recursor*, not a `projInfo` — so the whole
  projection-table story lands in `rec_rules`, not `proj_ok`.  The
  bridge's `ProjOkT` is therefore untouched by `DeclIndTT`.

### 14.3 The five semantic obligations, named in advance

Tier B reduces to five, and they are already isolated in the model
behind `_of_bottom` interfaces:

| obligation | model size | what it establishes |
| --- | --- | --- |
| `IndBottomPlainTT` | 1 518 | a plain rule's canonical iota LHS and its rhs agree |
| `IndBottomNestedTT` | 1 811 | ditto at stored level/parameter pins |
| `ProjBottomTT` | 960 | ditto for a projection function, at the fresh extension |
| `EtaFoldTT` | 553 | the checked `_model.eta` theorem becomes the fired eta law |
| `UnitFoldTT` | 510 | the checked `_model.unitlike` theorem becomes the unit law |

`modeled_bottom_plain` + `modeled_bottom_nested` alone are **63 % of
`IndInstall.lean`**, and they are near-duplicates differing only in how
the constructor spine is formed.  So the honest estimate is *five*
named `Prop`s, two of which dominate — and the split across sessions is
along those five, not along the files.

**The `_of_bottom` tails are already provenance-free and already shared
with the direct-struct path**, which is the same "written once, used by
two consumers" shape `eta_rescue` had (§6).  If the bridge keeps
`ruleLhsParts`/`TeleTyped` signatures — it does — those tails
transpose rather than being re-derived.

### 14.4 `DeclBasisTT` should be markedly cheaper than the model's

Tier C is 13 485 lines, but the bridge's version drops two of the three
theorem families per constant:

| model family | bridge |
| --- | --- |
| `interp_<c>_type` | `denote` of the pinned type — computation, but against `BConst.type`, which the layer already fixes |
| `<c>_key` | `HasType.const` for the six pinned formers that survive in `BConst`; a fired law for the four the layer derives (§11) |
| `annotOk_<c>_type` | **gone** |

And the `.basisDecl` case is `installBasisDecl` folded over `kind.declsA`
— a three-line duplicate check with **no inversion lemma in the model
either** (it is inverted inline).  So `DeclBasisTT` is a fold plus one
`extendBasisTT` per constant, which is the shape `extendValueTT` and
`extendAxiomTT` already have.

#### Scouted (2026-08-26), and one claim above is worse than stated

The model side was measured before grinding, per the discipline that
paid at iota and at div/mod.  Three results change the plan.

**There is no per-block install lemma to transpose — for five of the
six blocks.**  Only `installQuotBasis_sound`
(`Setlec/Model/Basis/Quot/Consistency.lean:23`, 479 lines) exists.  The
other five blocks' drivers are *open-coded inline* in
`Setlec/Model/Consistency.lean:777–1841` — 1 057 lines of driver, of
which ~130 are pure inversion boilerplate (the same `simp only` incantation
and one `by_cases … .isNone` group per constant, with the growing `Env`
prefix written out literally) **duplicated six times**.  So the bridge
does not cite a driver here; it writes one.  That is a cost the earlier
estimate did not carry — and also an opportunity, because writing it
*once* (a `BasisChain` relation plus a single fold inversion) is
strictly less work than the six copies the model has.

*A suggestion, not an obligation:* if the model side ever de-duplicates
those six drivers, the bridge's `BasisChain` + `foldlM_installBasisDecl_inv`
is the template — the relation is `V`-free, so it could be shared
outright under #123's criterion rather than re-derived.

**The obligation buckets, measured** (13 485 lines over six blocks):

| bucket | lines | share | bridge |
| --- | ---: | ---: | --- |
| `annotOk_<c>_type` | 2 626 | 19 % | gone |
| `annotOk_<c>_rhs` + frame minors | 3 004 | 22 % | gone |
| iota / `_ruleOk` / `*Val_fold` | 3 433 | 25 % | **transposes** to `hheadRec` |
| value / frame / universe support | 2 464 | 18 % | re-derived, not transposed |
| `interp_<c>_type` / `_rhs` | 799 | 6 % | **transposes** to `denote` computation |
| `<c>_key` | 441 | 3 % | collapses to `HasType.const` |

The `annotOk` family is **42 %** and all of it goes — not just the
`_type` half §14.4 named.  The `_rhs` half feeds `RecMemberOk`, and the
bridge's `hheadRec` wants the rhs's *denotation* and a `Deq`, never an
`AnnotOk`.  Against that, the support bucket (18 %) does **not**
transpose: it is infrastructure the model's own `interp` needs, and the
bridge's `denote` needs different infrastructure.

`<c>_key` is the one that collapses outright.  The model proves
`v₀ ψ ∈ˢ T` per constant; the layer has `HasType.const : HasType Γ
(.const c us) (c.type us)` **unconditionally**, so the bridge's version
is "the pinned kernel type denotes to `BConst.type`" — a computation,
with no membership argument at all.  That is the §14.4 prediction
holding at its strongest point.

**Per-block cost, and the order to take them:**

| block | model lines | note |
| --- | ---: | --- |
| Empty | 107 | `Empty.rec`'s rule list is `[]` — no iota obligation exists |
| PUnit | 812 | smallest block that exercises the *whole* `RecMemberOk` path |
| Eq | 2 489 | three of the four derived constants live here |
| Nat | 2 546 | |
| PSigma | 2 662 | the only block installing `projInfo`s |
| Quot | 4 763 | budget separately: 412 lines of universe arithmetic and 547 of value-level lemmas with no analogue elsewhere |

So: **Empty as the pilot** (it validates the driver and nothing else),
**PUnit as the first real block** (§14.5's item 2, now confirmed by
measurement rather than by guess), Quot last and priced on its own.

#### FLAG: four vacuous discharges are not four confirmations

`extendBasisTT`'s `hheadProj` and `hheadProjPair` have been discharged
by **constructor disjointness** in every block so far — `Empty`,
`PUnit`, `Eq` and `Nat` install no `projInfo`, so `ci = .projInfo entry`
is impossible and the obligations cost a `nomatch`.

By this document's own house rule that is **not evidence they are
stated correctly**: an obligation discharged vacuously has never been
*consumed*, so its shape is still a conjecture — the same status the
four derived λ-towers had before `Eq` elaborated them.  `PSigma'` is
the only block that installs `projInfo`s (`pairFst`, `pairSnd`), so it
is the first and only test of both clauses.

Flagged before writing it, on the same discipline as the constructor
level question (§14.4) and `Nat.rec`'s recursive occurrence: **if the
clauses are shaped wrong, `PSigma'` is where it shows**, and a
non-event there is only informative because it was predicted here.

> **THE FLAG FIRED — but one level up from where it was aimed.**  The
> two `proj` clauses are fine.  What is wrong is `extendBasisTT`'s
> **`hres : reservedBasisNames.contains ci.name = true`**, and it is
> *unsatisfiable* for the only two constants that would test them:
>
> ```
> reservedBasisNames.contains pairFstA.name = false   -- by decide
> pairFstA.name = projFnName psigmaName 0             -- by rfl
> ```
>
> `reservedBasisNames` lists twenty *names*; a projection function's
> name is `(T.str "proj").num i`, which is none of them — a fact this
> file already proves, as `projFnName_ne_reserved`, and uses to
> discharge `hheadEta`'s third disjunct.  **The wrapper assumes every
> pinned constant is reserved.  Twenty of the twenty-two are.**

The defect is §8.2's again, in the form the vacuity flag was written to
catch: a premise that four blocks satisfied for free, and that the
fifth cannot satisfy at all.  It was invisible for four blocks precisely
*because* those blocks discharged the clauses it guards by constructor
disjointness — the vacuity hid not the clauses' shape but the
**premise's**.

**RE-SIGNED.**  `extendBasisTT` no longer takes `hres`; it takes the
eta and unit-like head obligations as *parameters*, and
`basisEtaVacuous` / `basisUnitVacuous` supply them from reservedness for
the twenty constants that have it.  The `hpin`/`hdirect` pair stays,
unconditional — for an unreserved constant both are vacuous anyway
(`pinnedDirectT` is `none` there, and a `projInfo` is not a basis
kind), so nothing is lost by not gating them.  Thirteen call sites, one
helper pair each, and **no landed block's content changed**.

The rejected alternative was a sibling wrapper for the two entries.  It
would have preserved a signature we now know misdescribes the lemma:
**a premise that is false on part of the intended domain is not a
convenience, it is a misdescription**, and `projFnName_ne_reserved` —
proved in the same file for another purpose — is the fact that refutes
it.

> **A fix that shrinks in the hand is confirming the diagnosis; one
> that grows is suspect.**  This is the third instance: narrowing
> `RecRulesTT` made the transport *easier* and deleted three rescues;
> strengthening `CtxOk` cost its callers nothing; and this re-signing
> came out smaller than the finding suggested, because `hpin`/`hdirect`
> turned out to need no gating at all — both are vacuous on an
> unreserved constant anyway.  When the implementation keeps finding
> that less is needed than the diagnosis predicted, the diagnosis was
> about the right thing.

**Sharper than the flag predicted, and worth the rule.**  The flag said
"an obligation discharged vacuously has never been consumed, so its
shape is conjecture".  True, but incomplete: *the hypotheses a vacuous
discharge lets you get away with are conjecture too*, and they are the
harder half to notice, because nothing in the four passing blocks points
at them.  A vacuously-discharged obligation should be read as putting
**its whole surrounding signature** on probation, not just its own
statement.

One thing already known from reading the declarations, which the
clauses will have to fit: a `projInfo`'s `toConstantVal` is
`⟨projFnName e.structName e.idx, e.levelParams, e.ty⟩` — the entry
carries *its own* type, rather than borrowing the parent's, so the
`htype` obligation reads `e.ty` and the two pinned entries are
`native := true`.

#### The test ran: the clauses were right, the premise was not

`extendPairProjTT` installs either pinned projection, and the two
flagged obligations are **consumed**, not sidestepped:

* `hheadProj` takes `entry.native = true` and returns the entry's
  identity plus the two stored parents — every conjunct comes straight
  from the entry's own facts;
* `hheadProjPair` is the entry's `native` flag, read back.

Neither needed reshaping.  So the flag's aim was wrong and its firing
was right: **the clauses it doubted are correctly stated; what was
wrong was the premise the vacuous discharges let stand.**

> **A fired flag's value is the investigation it forces, not the
> accuracy of its aim.**  This one pointed at two clauses and found a
> premise one level up.  Had it been scored on aim it would read as a
> miss; scored on what it produced — a re-signed lemma, a rule about
> vacuous discharges putting whole signatures on probation, and a
> confirmation that the doubted clauses were fine — it is the most
> productive flag of the six raised so far.

**`hheadEta` at an unreserved head is the one thing that cost new
content.**  All three disjuncts are refutable, but only two of them the
way the reserved case does it:

1. `T = ci.name` — the extended environment then answers with a
   `projInfo` where an `indInfo` was demanded;
2. `caps.etaCtor = ci.name` — `EtaFamilyStoredT` demands a `ctorInfo`
   there, and gets the same `projInfo`;
3. `projFnName T j = ci.name` — **this one is new.**  For a reserved
   head it was `projFnName_ne_reserved`, immediate.  For a projection
   head the equation is *satisfiable*, and refuting it needs
   `projFnName_inj`: the name determines its parent, so `T = PSigma'`,
   which **is** reserved, contradicting the clause's own
   `reservedBasisNames.contains T = false`.

One lemma, and it is the exact shape the four vacuous blocks could
never have called for.

**And this is the first pre-registered flag to *fire*.**  Every earlier
one — the constructor level question, `Nat.rec`'s recursive occurrence —
resolved as a confirmed non-event.  A practice whose flags only ever
confirm would be suspect by this document's own metric rule (*a metric
that only ever succeeds measures nothing*); a firing, one level up from
where it was aimed, is the practice validating itself.

**Four of six landed** — `Empty`, `PUnit`, `Eq`, `Nat` — at ~2 230
lines of `DeclBasis.lean` against the model's ~5 950 for the same four
blocks.  The ratio holds at the 2.8× `PUnit` measured, and the shared
kit is why: `BetaSpine`, the `instantiate1` equations,
`denote_const_pin`, `substFn_param_self`,
`instantiateLevelParams_self`, and the depth-and-levels form of the
type computations were each written once and used by every block after
the one that motivated them.  `Nat`'s block lemma compiled on first
write, which is the kit's clearest single measurement.

**Two figures for the final accounting**, both of which have now
survived enough instances to be rates rather than anecdotes:

* **the 2.8× ratio**, holding across four blocks of *very different
  character* — a pilot with no rules, a block with one rule and an eta
  law, a block of three derived λ-towers, and a block with two rules and
  a field.  A single-block measurement becoming stable across that
  spread is what turns "the bridge is cheaper" into a number one can
  price the remaining work with;
* **first-write success under an accumulated kit** — §8.4's own
  metric, introduced at the div/mod assemblies (seven of nine) and
  still discriminating: `Nat`'s block lemma needed no iteration
  because every piece it wanted had been hoisted when an earlier block
  forced it.  It discriminates because it *fails* when the kit is
  incomplete, which is how `Eq.rec` was diagnosed as needing the
  depth-and-levels generalisation.

**Landed: the driver, the pilot, and `PUnit`**
(`Setlec/TTVerify/DeclBasis.lean`).
`BasisChain` + `foldlM_installBasisDecl_inv` replace the model's six
inline copies; `extendBasisTT` is `EnvTT.cons` at a pinned constant with
**six head obligations discharged by computation on the reserved-name
list**, which is what that list is for.  Three of the six are worth
naming, because they are the reason a basis install does not have to
reason about eta at all:

* `hheadUnit` and `hheadEta`'s first disjunct want a family whose name
  is *not* reserved, and a basis constant's is;
* `hheadEta`'s second wants an eta capability whose constructor is the
  constant being installed — and `EtaFamilyStored`'s **own first
  conjunct** rules out a reserved-named constructor.  That conjunct is
  documented in `Setlec/Verify/EnvGuards.lean` as existing "to keep the
  basis installs' head obligations vacuous by computation", and this is
  the install that collects on it;
* `hheadEta`'s third wants a projection-function name, and `projFnName`
  builds a `Name.num` node where every reserved name is a `Name.str`.

The `Empty` block is then two `extendBasisTT` calls, ~120 lines total.
Its whole content is one `htype` computation per constant, because
`Empty.rec`'s rule list is `[]` — so it validates the driver, the
`hEc`-style "the block's earlier constants denote to their pins" step
(now factored as `denote_const_pin`), and nothing else, exactly as
intended for a pilot.

#### `PUnit`: the first `hheadRec`, and what it cost

**~290 lines against the model's 812** — a 2.8× ratio, which is the
first real measurement of the per-block estimate and the number
Eq/Nat/PSigma should be priced against.  The saving is where §14.4 said
it would be: no `annotOk` family, and `<c>_key` collapsing to
`HasType.const` plus a denotation computation.

Two findings from it that the remaining blocks inherit.

> **The rule's constructor spine carries an arbitrary level.**  Nothing
> in `hheadRec` ties the `usj` the major premise is built at to the `us`
> the recursor is read at — the telescope says only that the spine
> *inhabits* the major domain.

For `PUnit` the gap closes with `punitEta`, which equates any two
`PUnit` elements at any two levels, so the iota rule fires after one
congruence step.  **`Nat` and `PSigma` have no such law**, and this is
the shape to look at first when they are written: either their
telescope premise pins the level after all, or the fired rule has to be
stated to tolerate the mismatch.  Better to know it now than to
discover it at `Nat.rec`.

#### The constructor-level question, answered before `Nat`

Asked at `PUnit` and answered by reading the pins and the firing code
rather than by building machinery.  **The distribution is the design
datum**, so here it is in full:

| block | constructor `levelParams` | freedom? | closure |
| --- | --- | --- | --- |
| `Empty` | — (no rules) | question does not arise | — |
| **`Nat`** | `Nat.zero`, `Nat.succ`: **`[]`** | **none** | unrepresentable |
| `PUnit` | `PUnit.unit`: `[u]` | yes | `punitEta` |
| `Eq` | `Eq.refl`: `[u]` | yes | `proofIrrel` |
| `PSigma` | `PSigma'.mk`: `[u, v]` | yes | `psigmaEta` then `projFstMk`/`projSndMk` |
| `Quot` | `Quot.mk`: `[u]` | yes | none of the above |

**`Nat` needs nothing.**  Its constructors bind no levels, so
`usj.length = cvj.levelParams.length` forces `usj = []`, the
substitution is the identity, and the constructor spine is a single
term.  The mismatch is *unrepresentable* exactly where the eta rescue
is unavailable — the pin's monomorphism doing for `Nat` what
`punitEta` does for `PUnit`.  By §8.4's taxonomy this is an
**undesigned coincidence**, not a forward provision: nobody made `Nat`
level-monomorphic to help this proof; Lean's `Nat` simply has no
universe parameter.

**`Eq` is cheaper still, and for a reason worth naming.**
`HasType.proofIrrel`'s two sides *need not inhabit the same* `Prop` —
a weakening adopted because soundness reads `mem_univ_zero` of each
side independently and §2.4 forbids a premise soundness never consumes.
That weakening, made for an unrelated reason, absorbs the level
mismatch for free.  A **second forward provision**, and one whose
author was solving a different problem.

**`PSigma` costs two steps rather than one**: `psigmaEta` rewrites the
major at the *recursor's* levels, then `projFstMk`/`projSndMk` recover
the fields at the *constructor's*.

> **FINDING — and `Quot` is the reason to look, not the reason to
> build.**  `Quot` has no eta law and is not a `Prop`, so it lands in
> none of the rows above.  Applying the fallback ladder to it turned up
> something about *all* of them: the checker's iota step **already
> guards on the level relation**.  `Setlec/Kernel/Core.lean:1281` fires
> only `if Level.isEquivList usj (recFireComparands …).1`, where the
> comparand list is `cvjLps.map (Level.subst lps us ∘ .param)` — the
> constructor's levels *derived from the recursor's*.

So `usj` is not free at all: the checker never fires at an unrelated
one, and `isEquivList` means the two lists agree **after `Level.eval`**
— the very thing `denote` applies.  The mismatch is therefore not
merely closable, it is *denotationally invisible*.

Which makes `EnvTT.cons`'s `hheadRec` **over-strong**: it quantifies
over every `usj` of the right length where the checker supplies only
the comparand one.  §8.2's recurring defect, fourth instance — and this
time the cost of the defect is visible in advance, because with the
premise added, `PUnit`'s `punitEta` step, `PSigma`'s two-step eta and
`Quot`'s open question **all disappear at once**.

> **The mismatch is denotationally invisible.**  `isEquivList` means
> agreement after `Level.eval`, and `Level.eval` is exactly what
> `denote` applies.  The checker's guard and the denotation's
> evaluation are the *same comparison* — the two-artifacts-one-object
> pattern again, and this time it dissolves an entire rescue
> apparatus.

**NARROWED (landed).**  `RecRulesTT`, `RecRulesTT.cons`,
`EnvTT.cons`'s `hheadRec` and `rec_rules_fire` now carry

```
Level.substFn φ cvj.levelParams usj
  = Level.substFn φ cvj.levelParams
      (recFireComparands rl cv.levelParams us cvj.levelParams [] rP).1
```

— the fire site's own test, in the form `denote` consumes it.  Three
things about how it went are worth keeping.

* **The inversion already had the fact.**  `iotaRec_inv`
  (`Setlec/Verify/InferLemmas.lean:711`) exposes the `isEquivList`
  conjunct; the sole consumer, `IotaStep.lean`, was discarding it with
  a `-`.  So the narrowing cost one named hypothesis and two lines at
  the fire site: `Level.substFn_congr (Level.isEquivList_sound hlev φ)`,
  which is *the same step the set model already takes*
  (`Setlec/Model/Core/Iota.lean:455`).  The bridge had simply
  transposed a stronger statement than the model's.
* **The argument list had to come out.**  `recFireComparands` takes the
  recursor's arguments, but **neither branch's level component reads
  them** — so the law quotes it at `[]` and
  `recFireComparands_levels` bridges the fire site's own list.  Stating
  it otherwise would have made the premise unquotable at the install,
  where no arguments exist.
* **It is the transport rule's own test.**  A hypothesis is legitimate
  exactly when the actual caller can discharge it; the caller here is
  the transpose of the code performing the guard, so the narrow form
  was always the provable one.

**And the payoff was immediate**: `PUnit`'s `punitEta` step came out of
`extendPUnitRecTT` the same hour, because the constructor's valuation
is now at the recursor's own level rather than an unrelated one.
`PSigma`'s two-step eta and `Quot`'s open question never had to be
written.

#### The same defect again, one line down — and this one was fatal

`Quot`'s open question came back anyway, and from the *other* half of
the same call.  `iotaRec` runs **two** comparisons before it fires:

```
if ← Level.isEquivList usj  (recFireComparands …).1 then
if ← defEqList (margs.take rl.ctorParams) (recFireComparands …).2 then
```

The second one checks the fired constructor's **parameters** against
the rule's comparands — for a plain rule, `args.take rl.ctorParams`,
the recursor's own leading arguments.  `iotaRec_inv` exposes it as the
conjunct immediately after the level one, and `IotaStep.lean` was
discarding *both* with a `-`; the narrowing above took the first and
left the second in place.  §8.2's fifth instance, one line below the
fourth.

**Why this one is different from the other four.**  The first four were
*wasteful*: the law quantified over instantiations no fire site
supplies, and the cost was rescue apparatus that could be deleted once
the premise arrived.  This one is **fatal**.  A stored recursor's rule
right-hand side reads the constructor's *fields* at the **recursor's**
parameters — that is what `args.take rP ++ margs.drop ctorParams`
means — so proving the law needs `⊢ field : recursor's parameter`
while the constructor's telescope gives `⊢ field : constructor's
parameter`.  The layer has **no type uniqueness**, so the two cannot be
bridged from inside; the premise is not an optimisation, it is the only
route.

It went unnoticed for four blocks because each dodged it for its own
reason: `Nat` and `PUnit` have no constructor parameters, `Eq`'s rule
drops all of them (`ys.drop 2 = []`), and `PSigma'` was carried by a
*congruence* — the right-hand side's two field slots were moved onto
`p.1`/`p.2`, which the projection rules type at the recursor's
parameters directly.  `Quot` has parameters, keeps a field, and has no
projections.  It is the first block that cannot dodge, and the last
one written.

> **The rule.**  A vacuously-discharged obligation puts its signature
> on probation (recorded above).  This adds the sibling: **a discarded
> conjunct puts the neighbouring conjuncts on probation too.**  The
> destructuring pattern that drops one fact usually drops the ones
> beside it, and they are exactly the facts a proof will later find it
> cannot do without.  The tell is a `-` next to a named binder in an
> inversion, not the named binder itself.

**NARROWED (landed).**  `RecRulesTT`, `RecRulesTT.cons`,
`EnvTT.cons`'s / `extendBasisTT`'s `hheadRec` and `rec_rules_fire` now
carry

```
RecRule.fire rl = .plain →
  ∀ i, i < RecRule.ctorParams rl → i < mI →
    Deq Δ (ys.getD i default) (xs.getD i default)
```

— the parameter test, denoted.  Three shape decisions, each forced:

* **Guarded on `.plain`.**  A nested rule's comparands are its stored
  pins, not the recursor's arguments; guarding keeps the premise
  faithful and imposes nothing on the nested path.
* **`i < mI` as well as `i < ctorParams`.**  The checker's comparand
  list is the recursor's *whole* argument list including the major, so
  a faithful unguarded statement would have had to carry the major's
  slot and, with it, the `Deq` between the major as written and the
  major in constructor form.  Restricting to indices below the major
  keeps the premise inside `xs`, where both the fire site and every
  install can read it.  Nothing is lost: `ctorParams ≤ mI` at every
  real recursor.
* **Stated `Deq`, not equality.**  `defEqList` is a *definitional*
  check; its transpose is `Deq`, and `Deq.conv` is exactly what the
  install needs to retype a field at the recursor's parameter.

**It is the family's first *fatal* instance, and the mechanism is the
project's oldest theme.**  The other four were wasteful — a premise
arrived and rescue apparatus became deletable.  This one made two
obligations *unprovable*: a field typed at the constructor's
parameters, needed at the recursor's, with no type uniqueness to
bridge them.  That is **domain pinning** in new clothing — the same
shape as the model's junk-agreement problem, as `annotate`'s
value-transparency requirement, as the `AnnotOk` proj clause — and as
always the only thing that pins the domain is *the checker's own
comparison*.  The bridge cannot invent the pin; it can only stop
throwing it away.

> **The sweep this earns.**  The sibling rule (a discarded conjunct
> puts its *neighbours* on probation) is the fourth-row tell sharpened
> into a search pattern, so it was run over the whole bridge: every
> `obtain ⟨…⟩ := …_inv …` whose pattern contains a `-`.  **Seven sites,
> and `iotaRec_inv` is six of the discarded conjuncts on its own.**
> Of the rest, four are shape facts (`stripPis … |>.isSome`,
> `piResidual … = some _`, `cbody.getAppFn = .const _ _`) — statements
> that the stored types have enough binders, not guards a law could
> quantify past.
>
> **One is a comparison, and it is the same shape one level up.**
> `iotaRec` runs a *third* check: `defEqList (residual.getAppArgs.drop
> ctorParams) ((args.take mI).drop rP)` — the recursor's **index**
> arguments against the constructor's canonical index tuple.  Every
> basis block has `rP = mI`, so the right-hand list is empty and the
> check is vacuous; that is exactly why five blocks could be written
> without it.  **Indexed modeled inductives are not vacuous**, and
> `DeclIndTT`'s five obligations are where they land.  Expect the
> parameter finding to repeat there verbatim, with *indices* in place
> of parameters — and expect it to be fatal again for the same reason.
> Check it before writing the five, not after.

#### The check, done — and the answer is in the model's own tower

**Confirmed: the index premise is needed, and the model shows why the
model never needed it.**  `ruleLhsAux` (`Setlec/Model/Interp.lean:319`)
builds the canonical iota redex as

```
mkAppN (.const n us)
  (fvsP ++ crest2.getAppArgs.drop ctorParams ++ [ctor spine])
```

— the recursor's **index slots are filled with the constructor's
canonical index tuple**, which is *literally the same expression* the
checker's third `defEqList` compares against
(`residual.getAppArgs.drop rl.ctorParams`).  `RecRulesOk`'s docstring
says so in words ("applied … to the prefix, **the canonical index
tuple** and the constructor spine"); the definition says so in code.

So the tower form **never quantified over the recursor's index
arguments at all** — it hard-codes the canonical ones.  The fired form
does quantify, and the extra generality is exactly one comparison wide.
That is the third inversion of the same mechanism, and the first one
*predicted* rather than discovered: levels (fourth instance),
parameters (fifth, fatal), indices (sixth, and fatal for the same
reason — a modeled recursor's rule right-hand side drops the index
slots entirely, so the law's two sides disagree on them unless the
premise identifies them).

> **The rule this settles.**  Wherever the model states a law over a
> *hard-coded* canonical form and the bridge restates it over a
> *quantified* one, the difference is a checker guard — and the guard
> is the only thing that can pay for it.  The three instances are
> `recFireComparands.1` (levels), `recFireComparands.2` (parameters),
> and `ruleLhsAux`'s index tuple.  There are no others: `iotaRec` runs
> exactly three comparisons.

#### The family is CLOSED, and that is a different kind of knowledge

`iotaRec` runs **exactly three** comparisons before it fires — levels,
parameters, indices — and each one is a fact the fired law needs and
the tower form did not.  All three are now identified, two threaded and
one predicted with its shape and its cost written down.  So:

> **No fourth narrowing exists to find.**  This class of defect is
> *done* for the iota path.

That is worth stating separately from the individual findings, because
a closed family is not the same kind of knowledge as an open pattern.
An open pattern says "look here again"; it never stops costing
attention, and it never tells you when you are finished.  A closed one
says "there is nothing further here", and the closure is *by
construction* — it rests on counting the guards in `iotaRec`, not on
having stopped finding instances.  The sixth instance was **predicted
from the enumeration** rather than discovered by a proof failing, which
is what makes the enumeration trustworthy: it produced a hit before it
was consulted for reassurance.

The **sweep** closes the same question one level out.  Every
`obtain ⟨…⟩ := …_inv …` in the bridge whose pattern drops a conjunct:
seven sites, six of the discarded conjuncts belonging to `iotaRec_inv`
alone, and the remainder shape facts (`stripPis … |>.isSome`,
`piResidual … = some _`, `cbody.getAppFn = .const _ _`) rather than
guards a law could quantify past.  The probation the sibling rule
imposes on neighbouring conjuncts is therefore **discharged for the
whole bridge**, not just for the one inversion that raised it.

> **AND THE PHASE-SPINE PATTERN PREDICTS ITS FORM.**  Each phase of
> this bridge has needed exactly one shared piece before any of its
> cases could be written, and it is always the one that **moves a
> spine between two descriptions of the same telescope**: `BetaSpine`
> for the basis blocks, `VTeleTyped.retarget` for the folds.  Applied
> forward, the bottoms' shared piece must be whatever moves the
> *constructor* spine between the rule's description and the fired
> redex's — which is precisely where this premise lives.  So the index
> plumbing is **not a second cost on top of** the bottoms' spine
> lemma; it *is* that lemma.  Budget one piece, not two.

**Not threaded yet, deliberately.**  The fourth and fifth narrowings
were each done with the consumer in hand — `PUnit`'s eta rescue, then
`Quot`'s field — and the playbook's own criterion is that *a hypothesis
is legitimate exactly when the actual caller can discharge it*.  Here
the caller is `IndBottomPlainTT`, which is not written.  The premise
also costs real plumbing the other two did not: a `VExpr`-level
`getAppArgs` (there is none) and a `denote`-commutes-with-`getAppArgs`
lemma, or an equivalent reformulation through `restC`.  Both decisions
— the exact form, and whether to spend that plumbing or reformulate —
belong with `IndBottomPlainTT`, not before it.  `EtaFoldTT` and
`UnitFoldTT` do not touch iota and can be written first.

**Confirmed in use at `Quot.ind`.**  Its iota is one line of the new
premise and then *proof irrelevance*: the stored motive's codomain is
`Sort 0`, the layer carries no `quotIndMk` rule, and both sides are
therefore simply proofs.  The premise's whole job is
`Deq.conv hya hp0` — the field `a`, typed at the constructor's `α` by
its own telescope, retyped at the recursor's.  Without it there is no
step; with it the rest is bookkeeping.  (`Quot` also confirms the
inverse reading of §11's four *derived* eliminators: `Quot.ind` is a
fifth, derived not from an equational law but from the collapse.)

#### `Eq`: the deferred towers, elaborated

§11 deferred four valuations — `Eq`, `Eq.refl`, `Eq.rec`, `PSigma'.rec`
— on the house rule that *a definition is a conjecture until a
consumer elaborates it*, and refused to write them until an install
needed them.  This is that install, and the first tower is landed:

```
eqValT ψ = λ (α : Sort u) (a : α) (b : α). eqE α a b
```

**§11's law is now a theorem about the tower, not an assumption.**
`EqLawTT` at the installed valuation is `eqValT_law`: three β-steps and
the lift absorptions they leave.  What the deferral bought is visible
in the proof — the tower was written *knowing* which three typings its
consumers had (§11 predicted the app-argument certificate would supply
exactly them), so the law's premises are the β-rule's premises and
nothing more.

Two structural facts about this block, both consequences of the layer
*deriving* the equality rather than carrying it:

* **`HasType.eqType` is premise-free** (`HasType Γ (.eqE T a b)
  (.sort 0)` with no side conditions), so `Eq`'s own typing is three
  `lam`s over one axiom — the cheapest `htype` in any block.
* **The block's iota will be β, not a computation rule.**  `Eq.rec`'s
  stored rule returns its minor premise, and the valuation that types
  it does the same; so where `PUnit` needed `punitRecUnit`, `Eq` needs
  only the β-chain it already has.

  **That is a long-range payoff, and worth the cross-reference before
  it is lost.**  `Eq.rec` is absent from `BConst` because it is
  *derivable* — `eqRec_derivable` in `Setlec/TT/Examples.lean`,
  established in the layer's first week (`Setlec/TT/DESIGN.md`, "Four
  constants of the checker's basis are absent because they are
  derivable"), on the argument that transport is the identity and
  `congrEq` retypes the canonical proof.  That decision was made to
  *shrink `BConst`* and remove the most index-heavy dependent types
  from `BConst.type`.  Its bill comes due here, months later, in a
  currency nobody was pricing at the time: **the block whose eliminator
  the layer declined to carry is the block whose install has no
  computation obligation.**  Cheap `BConst` then, cheap basis install
  now.

`Eq.refl` lands with it: `λ α a. prf`, typed by `HasType.refl` and
`conv`'d along `eqValT_law` **backwards** — the law is used in both
directions within the same block, which is the sense in which stating
it as a law rather than as a valuation equation (§11's ruling) was the
load-bearing choice.  `substFn_param_self` is the small fact every
basis type needs: a declaration read at its *own* level parameters is
read at the ambient assignment.

**All three towers are elaborated and typed** (`eqValT`, `eqReflValT`,
`eqRecValT` with `eqValT_law`, `eqValT_sort`, `eqReflValT_typed`,
`eqRecValT_typed`).  `Eq.rec`'s typing is the derivable-eliminator
shape in full: its body has the motive at `a` and `Eq.refl` where the
motive at `b` and the hypothesis is wanted, and two `congrApp`s close
the gap over

* `a ≡ b`, **read off the hypothesis** by pushing its stored-`Eq` type
  through the law and taking `Deq.intro`, and
* `Eq.refl α a ≡ t`, by `proofIrrel` — the two proofs need not inhabit
  the same `Prop`, which is the #127 relaxation paying out again, now
  in the same block whose install it also rescued from the level
  question.

The frame is factored as `eqRecCtx` rather than written six times; that
is worth noting only because the six-entry context appears in eight
statements and the factoring is what made the proof readable.

**`BetaSpine` is the block-independent half of every iota.**  Each
basis block's rule is a λ-tower applied to the fire site's spine, and
each would otherwise spell out its own chain of partially-instantiated
towers — the intermediates being exactly what is tedious and exactly
what nobody reads.  `BetaSpine Γ f args r` records the chain
(`HasType Γ x A` per binder, the body instantiated as it goes) and
`Deq.ofBetaSpine` collapses it to `Deq Γ (mkAppN f args) r`.

So a block's iota obligation becomes **building the relation**, and the
telescope's own typings are what build it: `VTeleTyped`'s `cons` gives
exactly the `HasType Γ x A` that `BetaSpine`'s `cons` wants, at exactly
the instantiated domain.  Written for `Eq`, it costs `Nat`, `PSigma`
and `Quot` nothing — the same pilot-then-blocks economy the
`instantiate1` kit had.

#### Three shared pieces, found the same way

`BetaSpine`, the `instantiate1` kit and the depth-and-levels form of the
type computations were each found by the same move: **hit it in one
block, recognise that every block needs it, hoist it before writing the
second.**  The third is worth spelling out because it is the least
obvious.

A block's `htype` wants its pinned type denoted at depth `0` and at the
declaration's *own* level parameters; its `hheadRec` wants the same type
denoted at the fire site's depth `d` and at the recursor's `us`.  Those
look like two lemmas and are one: `denote_eqRec_type` is stated at
arbitrary `d` and arbitrary `[w1, w2]`, and the install's case is the
specialisation at `0` and `[param u_1, param u]`, where
`substFn_param_self` collapses the assignment back to `φ`.  Writing the
depth-`0` case first — as `PUnit` did — means writing the general one
afterwards anyway, and the general one is no harder.

The towers need a matching triviality (`eqValT_congr`): a valuation
reads the assignment only at its own level names, so the tower the
*type* mentions and the tower the *recursor* is read at are the same
term even though the two assignments differ elsewhere.

**A tally, because level erasure keeps paying and the entries are
scattered.**  `Setlec/TT/DESIGN.md` §2.2 makes universe levels ground
`Nat`s — no `VLevel`, no level substitution, no level-equality
judgment — on the argument that everything is denoted at a fixed
assignment.  What that has bought this bridge, so far:

1. **Level comparison is `Nat` equality.**  The checker's level defeq
   decides equality under *all* assignments, so at a fixed assignment
   the two ground levels are literally equal — the bridge obligation is
   `rfl`, not a lemma.
2. **The `hheadRec` mismatch is denotationally invisible** (§14.4).
   `isEquivList` is agreement after `Level.eval`, and `Level.eval` is
   what `denote` applies — the checker's guard and the denotation's
   evaluation are the same comparison *because* the target has no
   symbolic levels to disagree about.
3. **`eqValT_congr` is a `rw`.**  Two assignments agreeing at a
   constant's own level names give the *same term*, not merely
   equivalent ones, so no congruence lemma travels with the towers.

Three payouts from one erasure, and none of them was the reason for it
— §2.2's stated reason was avoiding a vestigial `φ` on the whole
semantics.

*The tally's format — decision, stated reason, actual returns — is the
one to reuse if another decision earns one.  What makes it worth
keeping is the third column: a decision that only ever pays in the
currency it was made for is unremarkable; one that pays in three others
is evidence the decision was tracking something real about the
object.*

#### A second decision earns the tally: `eqUpToNames`, not `==`

**The decision** (#105): the major pin comparing a preprocessed
declaration against its model companion is `eqUpToNames`, not
structural `==`.  **The stated reason** was narrow and defensive — the
preprocessor renames binders, so `==` would reject streams that are
correct.

**What it has actually bought**, in three places that had nothing to do
with binder names:

1. **The nested-aux certification** (#105) could pin a lowered
   `rP`-context rule at all.  Structural equality would have failed on
   the index-variable split, which is not a renaming.
2. **The projection audit** (#107) could state `annotateProjRec`'s
   permanence: the 113 accepting `Exists` uses in `init-full` match
   their templates up to names and *not* structurally.
3. **The modeled-inductive folds** (§14.3, in progress) get their
   public-versus-model telescope bridge from
   `checkMemberVal_inv`'s `eqUpToNames` — the public type former's
   domains against the model's, which is exactly the comparison the
   fold needs and exactly the one `==` cannot make.

Three payouts, none of them binder renaming.  The pattern matches the
level-erasure tally's: the decision was made in one currency and has
paid in three others, which is the tell that it was tracking the
object rather than the symptom.

> **THE FORMAT'S THESIS, PROVISIONALLY.**  Both entries share a
> stronger claim than either makes alone: *the stated reason was the
> least interesting thing about the decision.*  Level erasure was
> justified by avoiding a vestigial `φ`; `eqUpToNames` by binder
> renaming.  Neither reason predicts a single one of the six payouts
> between them.
>
> This is also **why the third column earns its keep**.  A record that
> tracked decisions by their stated reasons would make them all look
> interchangeable — every one is "because otherwise X breaks" — and
> would give no way to tell a decision that fits the object from one
> that merely patches a symptom.  The returns column is the only place
> that difference shows.
>
> *Two entries is a coincidence; a third would make it the format's
> thesis rather than an observation about it.  If one arrives, promote
> this box.*

#### The transposition recipe, as arithmetic

`Setlec/TTVerify/DeclInd.lean`'s header states the fold headers'
template, and it is worth naming here because the remaining folds
should each carry the same three-line count:

> Split the model theorem's hypotheses into **`V`-free syntactic**
> (find?s, `stripPis` shapes, telescope-domain matches,
> `hasFvar = false`) and **semantic**.  The syntactic ones are
> inherited *unchanged*.  The semantic ones are replaced one for one —
> `interpClosed`/`∈ˢ` → `denote`/`HasType`, `TeleFit` → `VTeleTyped`,
> the `Eq` former's value → `EnvTT.eq_law` — except `AnnotOk`, which
> **vanishes**.

`unit_rule_fold` is 12/9; `eta_rule_fold` is ~15/8.  Stating the count
before writing the proof is what turns "transpose it" from a hope into
a plan, and it is the same discipline as measuring the function you
invert (§0).

#### `Eq.rec`'s ingredients, complete

The wrapper's four computational inputs are landed:
`denote_eqRec_type` (any depth, any levels), `denote_eqRec_rhs` (the
rule's right-hand side, at the same four domains the type has),
`eqRecValT_typed`, and `eqRecValT_closed` — plus
`Expr.instantiateLevelParams_self`, which is what lets the install's
depth-`0`-own-parameters case be a specialisation of the general form
rather than a second proof.

**The block is landed**, and the assembly went as predicted: the
telescope's six typings, handed unchanged to two `BetaSpine`s — **six β
on the left against four on the right, meeting at the minor premise** —
and `Deq.trans`.  The domains line up by construction, so the six
`cases` that peel `VTeleTyped` produce exactly the six arguments
`BetaSpine.cons` wants, in order, with no adapter.

One thing the assembly forced, and it is the kind of thing to expect
again: `extendBasisTT` had to return **which valuation it installed**,
not merely that some `EnvTT` exists.  `Nonempty` erases the witness, and
the next constant in a block needs its predecessor's valuation — `Eq`'s
is the first that cannot be recovered from `BasisPinnedTT`, because
`Eq` is one of the four the layer *derives* and its `pinnedDirectT`
entry is `none` by design.  So the conclusion is now
`∃ m', m'.cval = cvalSet …`, and a block lemma threads the equations
forward.

> **THE DEFERRAL'S DEBIT.**  §11's decision to leave the four derived
> constants out of `pinnedDirectT` has been tallied generously — the
> towers' shapes could not have been guessed early, the law is
> bidirectional, the counterfactual is that writing them sooner could
> only have been right by accident.  The cost belongs in the same
> record: **a design decision to leave something unpinned propagates
> into the interface of the thing that installs it.**  Because the
> derived constants have no pin to read a valuation back from, the
> installer must *return* its valuation rather than merely assert an
> environment exists.  `Empty` and `PUnit` masked this completely —
> everything they install is pinned — so it surfaced only at the third
> block, one interface change and a threaded equation later.  Small,
> paid once, and invisible from the decision, which is exactly why it
> is recorded where the decision is praised.

#### The recursive occurrence, checked — and it needed nothing

`Nat.rec`'s `succ` rule is the first stored right-hand side in any
block that **mentions the recursor being installed**: it applies
`Nat.rec.{u}` to the motive, both minors and the field.  Flagged before
writing it, because no finished block contained the shape.

**It is expressible with no change.**  `EnvTT.cons`'s `hheadRec` states
the rule's denotation at `cval'` — the *post-install* valuation, in the
*extended* environment — and always did.  So the recursive occurrence
resolves to the constant currently going in, which is exactly what the
fired form needs.

Worth stating plainly because the tempting reading is wrong: this is
**not** a second payout of the returned-witness fix.  That fix solved a
different problem — threading a valuation from one constant of a block
to the *next* — and the recursive occurrence is within a single
constant's own obligation, where `cval'` was already in scope.  Two
adjacent problems with different answers, and conflating them would
have credited the fix with something the original design had right.

> **ATTRIBUTION DISCIPLINE.**  A *payout* claim needs the same evidence
> as any other claim.  An interface fix that appears to keep paying is
> precisely the shape to check **before** the claim is made rather than
> after — the reading is flattering, the two problems are adjacent, and
> the difference (threading *between* constants versus resolution
> *within* one constant's obligation) is invisible unless you look at
> both shapes side by side.

The same paragraph records the pre-registration's ordinary return: the
flag was a **non-event**, and a non-event is data only because it was
named as a prediction first.

**Confirmed in code** (`denote_natRec_succRhs`): the `succ` rule's
right-hand side denotes with its `Nat.rec` occurrence resolving through
`cvalSet … natRecA.name val` — one `cvalSet_self` rewrite, the same
step any *non*-recursive constant of the block takes.  The recursive
case is not a case.  Had the shape not been flagged, its
absence would have been indistinguishable from never having thought
about it.

*The general lesson in miniature*: an install lemma's consumer is the
**next install**, and what that consumer needs is the *state*, not the
existence.  A `Nonempty`-shaped conclusion is right only where nothing
sequential consumes it.  Checked across the bridge: the per-declaration
obligations (`DeclDefnTT` and its five siblings), the single-constant
installs (`extendValueTT`, the axiom and opaque cases) and the three
block lemmas are all consumed by the *fold*, which needs only an
`EnvTT` — so `Nonempty` is correct at every one of them.  The basis
chain was the sole sequential consumer, and it is fixed.

**A second candidate, filed unproved.**  The reason `denote_eqRec_rhs`
lands at *the same four domains the type has* is that **the stored rule
is the eliminator's own telescope re-abstracted**, so its binders are
the type's prefix.  If that holds for the other blocks' rules too — and
it should, since the preprocessor generates them the same way — it is a
fact about the *checker's rule format* doing bridge work, and belongs
in §8.4's list under the first kind.  `PUnit`'s rule is consistent with
it, but `PUnit`'s rule has one binder and proves nothing.  Confirm at
`Nat` (two rules, one with a field) and `PSigma` (two fields) before
adding it.

**The two candidates are not independent, and that is worth recording
before the test rather than after.**  If the stored rules were *not*
telescope re-abstractions, their right-hand sides would not abstract the
type's prefix, `BetaSpine`'s `cons` would not receive `VTeleTyped`'s
`cons`, and an adapter would be needed — which withdraws the
telescope-decomposition candidate too.  So:

* **joint confirmation** is strong evidence, because it is *one*
  underlying fact (the checker is telescope-shaped throughout) showing
  up in two places;
* **joint failure** is diagnostic rather than confusing — it localises
  the error to the rule format, not to the walk abstraction;
* **split outcomes** would be the surprising case, and would mean one of
  the two was misstated.

`Nat` and `PSigma` therefore test both at once, and a single adapter
withdraws both.

#### CONFIRMED at `Nat.rec`, and promoted to §0's third practice

> **Every telescope-shaped obligation in this bridge decomposes against
> the same walk.**  `TeleTyped` (the `Expr` side), `VTeleTyped` (the
> term side) and now `BetaSpine` (the reduction side) are three
> inductives with the same `cons`, and they compose without glue
> because all three are walking the checker's own telescope.

Filed as a candidate, then tested and confirmed — see §0's third
practice for the statement, the provenance and the arithmetic-versus-
adapter distinction the diagnostic needs.  What follows is the test as
it was set before the outcome was known.  **The test is
`Nat`, `PSigma` and `Quot`**: if their iota obligations decompose
against the same walk with no new relation and no adapter, the property
is real and belongs in §0's practice list — *the checker is
telescope-shaped throughout, so one walk abstraction serves all of it,
and a bridge obligation that does not decompose against it is a signal
the obligation is stated wrong.*  If any of the three needs an adapter,
the honest reading is that the coincidence was three instances of a
shape the `Eq`/`PUnit` blocks happen to share, and the candidate is
withdrawn.

**The computation needed a per-constructor `instantiate1` kit.**
`denote` opens every binder with `instantiate1` at cut `0`, so a basis
type's computation walks it once per node — and unfolding the
definition leaves a decidable `if` at each `bvar` that `simp` will not
take without help.  Seven `rfl` equations
(`Expr.instantiate1_bvar` … `_lam`) remove the problem for every block,
which is why `PUnit` paid for them and `Eq`/`Nat`/`PSigma`/`Quot`
will not.

**A finding for the model side, not this one.**  Five `<c>_iota`
theorems — `natZero_iota`, `natSucc_iota`, `eqRec_iota`,
`psigmaMk_iota`, `punitRec_iota` — have **zero consumers anywhere in
the repo**, 1 111 lines of them.  The real iota obligation is carried
by the `*_ruleOk` family.  Nothing should be ported from them, and the
model side may want them gone.

**And one caution above is now stale.**  §8.3 says `Installs`
"describes an *ordinary* install; a basis install is exactly what
violates its last three fields".  Since §8.5's second pass made
`LitAgree`'s seven equations **conditional on the guard holding in the
old environment**, `Installs.of_fresh` applies to a basis install too:
while a block is going in the guard is false (so the clauses are
vacuous), and once it holds every name the clauses mention is stored,
hence distinct from the fresh one.  What a basis install really changes
is *which literals denote at all* — which is what the `lit` field
exists to carry, not what it fails at.

### 14.5 What this buys, stated as a plan

1. **Relocate tier A** (or the ~1 500 lines of it the bridge needs) out
   of `Setlec/Model/Extend/*`.  Blocking; see §14.1.
2. `DeclBasisTT` **before** `DeclIndTT`: it is smaller than its model
   counterpart suggests, it exercises `extendBasisTT` and the §11 `Eq`
   law, and the pinned recursors' fired rules are the smallest instance
   of the same `RecRulesTT` head clause the big install needs.
3. `DeclIndTT` last, split along the five obligations of §14.3, with
   `EtaFoldTT`/`UnitFoldTT` first (they are the smallest and they close
   `CapsOkTT`, which `majorToCtor`'s rescues already consume).

#### Plan status (2026-08-27)

1. **Done** — `Setlec/Verify/Extend/*`, 3 934 `V`-free lines; see the
   gate note in §14.1.
2. **Done** — `DeclBasisTT` is discharged.  All six blocks:
   `Empty`, `PUnit`, `Eq`, `Nat`, `PSigma'`, `Quot`.  The prediction
   held on both counts: the block lemmas are a fold plus one
   `extendBasisTT` per constant, and the pinned recursors' fired rules
   *were* the smallest instance of the `RecRulesTT` head clause — small
   enough to be written five times, and the fifth (`Quot`) is what
   exposed the missing parameter premise the big install would have hit
   at full scale.  **That is the argument for step 2's ordering,
   restated as an outcome**: doing the small instance first did not
   merely warm up the machinery, it *audited* it.
3. **Next** — `DeclIndTT`, five obligations, `EtaFoldTT`/`UnitFoldTT`
   first.  `IndBottomPlainTT` carries the index premise (§8.2's sixth
   instance), designed in place rather than threaded blind.

`CheckDeclTT` now stands on five of its six obligations: `DeclDefnTT`,
`DeclThmTT`, `DeclOpaqueTT`, `DeclAxiomTT`, `DeclBasisTT`.


### 14.6 HANDOFF: what a successor needs that the code does not say

Written at the end of the run that discharged `DeclBasisTT`.  The
branch is `feat/119-ttverify-stage2`, the worktree is
`.claude/worktrees/ttv-stage2`, and master is merged `--ff-only` from
it (**from the repo root** — a bare `git merge --ff-only` *inside* a
worktree silently reports "Already up to date"; verify by comparing
SHAs, never by the merge command's output).

Gate procedure, mandatory for anything touching `Setlec/TTVerify/*`:

```
rm -f .lake/build/lib/lean/Setlec/TTVerify/*.olean
lake build 2>&1 | grep -E "^(error|warning)"      # must print nothing
lake test
```

The forced recompile is not superstition: Lean emits a file's warnings
only when it *compiles* the file, so an incremental build hides a
warning in a file it did not touch.  A warning escaped to master
exactly once, that way.

The arena / e2e / split-driver / infer-only gates were **not** re-run
during this run, and the argument is worth repeating rather than
re-deriving: every change was confined to `Setlec/TTVerify/*`, which
the checker never imports, so the checker's compiled output is
byte-identical and those gates cannot have moved.  The moment a change
touches `Setlec/Kernel/*` or `Setlec/Verify/*`, that argument lapses.

#### 14.6.1 The next lemma, designed

`UnitFoldTT`'s middle needs one piece, and it is the foundation all
five obligations stand on.

**What it does.**  Turn the install's *syntactic* description of the
checked theorem's statement into the *semantic* telescope a fold can
walk.  The pins give `tcv.type.stripPis (nP + 2) = some (sbinders,
sbody)`; the use site gives `denote cval env φ d tcv.type = some T̂`.
The lemma must produce a `TeleAlign` whose second residual is named —
`.pi Tm (.pi Tm' eqSpine)` — so the fold can peel the last two binders
by hand and land in `Deq.ofEqThm`.

**Shape** (approximate; fix it against the consumer, see the warning):

```lean
theorem teleAlign_of_stripPis (hcl : ∀ n ψ, VExpr.Closed (cval n ψ)) :
    ∀ (k : Nat) {e e' : Expr} {bs bs' : List (Name × Expr × BinderMeta)}
      {body body' : Expr} {d : Nat} {v v' : VExpr} {xs : List VExpr},
      e.stripPis  k = some (bs,  body)  →
      e'.stripPis k = some (bs', body') →
      (∀ j (b b'), j < k → bs[j]? = some b → bs'[j]? = some b' →
        b.2.1 = b'.2.1) →                      -- the pins' domain match
      denote cval env φ d e  = some v  →
      denote cval env φ d e' = some v' →
      xs.length = k →
      ∃ r r', TeleAlign v v' xs r r' ∧
        denote cval env φ (d + k) <opened body>  = some r ∧
        denote cval env φ (d + k) <opened body'> = some r'
```

**Induction structure.**  On `k`, unknown at the use site (it is
`caps.unitParams`).  Each step is: `denote_forallE` to expose
`.pi A B`, the domain match to identify the two `A`s, then
`denote_beta` (`Setlec/TTVerify/Inst.lean:186`) to see that the
instantiated codomain `B.inst x` is the denotation of the body with the
opened fvar substituted.  `denote_forallE` opens with `.fvar d n ty`
and steps `d` to `d + 1`; `stripPis` leaves binders *unopened*, so the
`k`-th binder's type has loose bvars and cannot be denoted at `d` —
that mismatch is the whole content of the lemma and the reason it is
not three lines.

**Estimate:** 150–250 lines.  Everything it needs exists: `denote_forallE`
(`Denote.lean:289`), `denote_beta` (`Inst.lean:186`), `denote_erasedEq`
(`Inst.lean:265`), `TeleAlign` and `VTeleTyped.retarget`
(`DeclInd.lean`).

> **WRITE IT FROM THE USE, NOT FROM THE HYPOTHESIS.**  This design
> space has punished the other order twice on `TeleAlign` alone:
> * `SameDoms.refl` was written by reflex and is **false** — a non-`∀`
>   type has no domains to agree about, so the relation is partial and
>   its witness must come from a *fitting*;
> * `SameDoms` then constrained only the domains, so `retarget` could
>   conclude only that *some* residual exists — precisely the fact a
>   fold cannot use, because the statement's telescope does not end
>   where the type former's does.
>
> Both were fixed by one question: **what will the consumer do with
> this conclusion?**  Ask it before writing the statement, not after
> the proof compiles.  Concretely: write `UnitFoldTT`'s proof skeleton
> with this lemma `sorry`ed, read off the shape the skeleton actually
> demands, and only then state it.

#### 14.6.2 The remaining-work map

In order, with consumers, frictions and the shared pieces each uses.

**1. `UnitFoldTT`** — consumer: `EnvTT.cons`'s `hheadUnit`, hence
`CapsOkTT`, hence `majorToCtor`'s zero-field rescue and the
proof-irrelevance path.  Statement pins: the *unit half* of `EtaPins`
(`Setlec/Verify/Extend/Iota.lean:917`), obtained via
`etaPinsT_of_caps`.  The statement is
`∀ p⃗ (x y : T._model p⃗), Eq.{ℓA} (T._model p⃗) x y`.
Shared pieces: `teleAlign_of_stripPis` (above), `VTeleTyped.retarget`,
`Deq.ofEqThmClosed`.  Model counterpart: `unit_rule_fold`
(`Model/EtaInstall.lean:581`), **12 syntactic / 9 semantic**.

**2. `EtaFoldTT`** — same skeleton.  The second subject binder is
replaced by `caps.etaFields` projection arguments, so the final spine
is `mkAppN (cval etaCtor …) (xs ++ projections)` instead of `B'`.
Model counterpart: `eta_rule_fold` (`Model/EtaInstall.lean:24`),
**~15 syntactic / 8 semantic**.

**3–4. `IndBottomPlainTT` / `IndBottomNestedTT`** — 63 % of
`IndInstall.lean` between them, and near-duplicates differing only in
how the constructor spine is formed.  **These carry §8.2's index
premise, and the cashed prediction says the premise's plumbing *is*
this phase's spine lemma** — the thing that moves the constructor spine
between the rule's description (`ruleLhsAux`, which fills the
recursor's index slots with the constructor's canonical tuple) and the
fired redex's (which leaves them free).  Budget one piece, not two.
The premise's form should be settled with `IndBottomPlainTT`'s skeleton
in hand, for the same reason as 14.6.1's warning; it will need a
`VExpr`-level `getAppArgs` (none exists) or a reformulation through
`restC`.

**5. `ProjBottomTT`** — the same at a projection function, which
`checkProjFn` stores as a *degenerate recursor*, so it lands in
`RecRulesTT` and not in `ProjOkT`.  `ProjOkT` is untouched by
`DeclIndTT`.

**Two known frictions, neither paid yet.**
* `RenEq` lives in `Model/TeleElim.lean` (blocked) but unfolds to
  `ErasedEq` from `Setlec/Verify/Subst.lean` (usable) — the bridge
  needs a one-line local definition or an inlining.
* The pins give domain equality against the **model**'s telescope while
  the folds want it against the **public** one.  The chain is
  `checkMemberVal_inv`'s `eqUpToNames` → `ErasedEq.stripPis_inv` +
  `stripPis_renameConsts_inv` (both in `Verify/`) → `denote_erasedEq`.
  This is `eqUpToNames`'s third payout (§ the tally) and the machinery
  to consume it already exists.

#### 14.6.3 Working memory a successor cannot recover from the record

**The annotated declarations are not the raw ones, and the difference
bites.**  `Setlec/Kernel/Basis/Quot.lean`'s raw `quotBasis` says
`fire := .inert` and `ctorParams := 0` for both quotient rules; the
*annotated* `quotIndA`/`quotLiftA` say `.plain` and `ctorParams := 2`.
Annotation **computes** those fields.  Reading the raw list cost a
whole design pass (`Quot.ind` was planned as iota-free).  *Always read
the `*A` declaration, never the raw block.*  Corollary: the `*A_eq`
lemmas (`psigmaRecA_eq`, `quotIndA_eq`, `quotLiftA_eq`) look like idle
documentation and are not — they are `rfl` **transcription checks**,
and `quotIndA_eq` caught a wrong binder-info on its first run.  Write
one for every rule you transcribe.

**`extendBasisTT`'s argument order** (all positional in the existing
`refine`s): `hheadEta`, `hheadUnit`, `hpin`, `hdirect`, `hfresh`,
`hwf`, `hclosed`, `hparams`, `htype`, `hnodefn`, `hnothm`, `hnoax`,
`hempty`, `hheadCtors`, `hheadRec`, `hheadProj`, `hheadProjPair`,
`hheadEq`.  Idioms: `hpin` is `(fun _ => by decide)` at a basis-kind
constant and `(fun h => nomatch h)` at an axiom; `hdirect` is always
`rw [show ConstantInfo.name cA = cName from rfl] at hp;
simp +decide [pinnedDirectT] at hp; exact hp`.

**Named `*RhsV` defs exist only to be `BetaSpine`'s `f`.**  On the
left-hand side `Deq.ofBetaSpine`'s head is inferred from the goal; on
the right-hand side it is not, so it must be supplied — which is why
`psigmaRecRhsV`, `quotIndRhsV`, `quotLiftRhsV` are separate `def`s
instead of shapes inlined in their `denote_*_rhs` lemmas.  Nothing in
the statements says this.

**Block lemmas build `EnvWF`; they do not receive it.**
`installBasisDecl` checks *only* freshness, so `BasisChain` carries
nothing about resolution.  Hence every block has `res2`/`res3`/… goals.
In those goals you must `rw [show <ci>.toConstantVal.type = <the
literal> from rfl]` before `simp [Expr.constsResolve, <find? facts>]`
— **do not** put the constant's `def` name in the simp set: `simp`
unfolds it in the *environment* too, and the `find?` hypotheses stop
matching.  That trap cost a cycle at three separate blocks.

**Elaboration gotchas, each of which cost at least one build cycle.**
* `Deq.conv`, never `HasType.conv (…).toHasType _` — the latter leaves
  the inert `T` slot un-inferable.
* `cval_pinned`'s `t` is implicit and determined by its `hpin`
  argument, so a `by simp` there cannot infer it: pass `(t := …)`.
* `Level.eval φ (Level.param n)` does **not** close by `rfl` in these
  goals; `simp [Level.eval]` does.
* `HasType.const` at the head of an application chain needs
  `(c := …) (us := …)`.
* `intro` cannot bind `-`; use `_`.
* For normalizing fired spines, `simp only [VExpr.inst, VExpr.liftN,
  Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
  inst_chain₁₋₄, inst_absorb₂₁₋₅₄, VExpr.liftN_zero]` — the four `Nat`
  simprocs must be spelled out or the `if i < k` guards do not reduce.
  Plain `simp` also works but may over-normalize `mkAppN`.

**An unstated ordering.**  Within a basis block the constants must be
installed in `declsA` order, and each install's `htype` needs the
*earlier* constants' valuations.  Two ways to get them, and the second
is much cheaper: thread `∀ ψ, m.cval n ψ = …` hypotheses along the
chain (what `Eq` does, because `eqValT` is not pinned), or call
`cval_pinned` from the invariant (what `PSigma'` and `Quot` do, because
they are).  Prefer `cval_pinned` whenever `pinnedDirectT` has an entry.

**Why `RecRulesTT`'s parameter premise looks the way it does** — the
statement alone will not tell you: guarded on `.plain` because a nested
rule's comparands are its stored *pins*, not the recursor's arguments;
restricted to `i < mI` because the checker's comparand list is the
recursor's *whole* argument list including the major, and a faithful
unguarded form would have had to carry the major's slot and with it the
`Deq` between the major as written and the major in constructor form.
Nothing is lost: `ctorParams ≤ rP ≤ mI` at every real recursor, and
`RecRulesOk` states the first half explicitly.

### 14.7 The `DeclIndTT` phase: the spine lemma, and the premise nothing supplies

Written after `UnitFoldTT` landed.  Two findings, one retraction and
one **open request**; the request is the reason the phase cannot be
finished without a ruling.

#### 14.7.1 The spine lemma, and why it is two lemmas

§14.6.1 designed `teleAlign_of_stripPis` as one induction from
`stripPis` to `TeleAlign`, with the residual named
`VExpr.instSeq xs (k-1) R`.  **That induction does not close**, and the
obstruction is §0's fifth tell firing a *second time on the same
relation*:

> `TeleAlign S S' ys r r' → TeleAlign (S.inst x j) (S'.inst x j) ys
> (r.inst x j) (r'.inst x j)` is **false**.

`inst_inst_comm` puts the two orders apart by `x'.inst x j` on the
*other* spine elements, and a spine fitted over an open `Δ` has some.
The relation is telling you, for the third time, that **the spine is
doing work**: the statement proved by induction must not mention it.

The fix is to slice one step earlier.  `PiTower k S S' R R'` is
`TeleAlign` with the spine deleted — two towers of `k` `.pi`s with
pairwise equal domains over bodies `R`, `R'`.  Then:

* `piTower_of_stripPis` is the syntactic induction, and it closes,
  because *a substituted tower is a tower* (`PiTower.inst`);
* `PiTower.teleAlign` fits the spine in one induction on `k`, where
  `VExpr.instSeq`'s recursion lines up with `TeleAlign`'s peel by
  construction — the outermost argument is substituted at cut `k-1` on
  both sides.

**The generalisable form.**  When a relation refuses to commute with
substitution, do not weaken the relation; find the *sub*-relation that
does, prove the induction there, and re-attach the part that does not
commute afterwards.  Here the part that does not commute is exactly
the part the consumer supplies.

#### 14.7.2 The machinery the phase actually needed

Named because §14.6.2 under-counted it, and the successor should
budget from the real list:

| piece | file | why |
|---|---|---|
| `denote_renameConsts` + `RenameOkT` | `Rename.lean` | the pins describe `T._model`; the laws are at the public former |
| `RenEqT` / `PiDomsRenEqT` | `Rename.lean` | restated from `Model/TeleElim.lean` (blocked) |
| `VExpr.instSeq` + 8 lemmas | `TeleOpen.lean` | the term-side half of the telescope walk |
| `openFvars`, `instSeq_instantiate1_in` | `TeleOpen.lean` | opening, and the `Expr`-side dual that was missing |
| `PiTower` + 3 lemmas, `VTeleTyped.retarget'`, `VTeleTyped.append` | `DeclInd.lean`, `Tele.lean` | §14.7.1 |
| `denote_paramTuple` / `instSeq_paramTuple` | `DeclInd.lean` | **the reusable core** |
| `denote_unitResidual` / `instSeq_unitResidual` | `DeclInd.lean` | the unit statement's residual |

**`*_paramTuple` is the piece to reuse.**  Every pinned domain of a
capability statement is the *same* thing — the model former applied to
the statement's parameter variables — at a bvar shift `c`.  The unit
statement uses `c = 0` (the `x` domain), `c = 1` (the `y` domain) and
`c = 2` (the equation's type slot); `EtaFoldTT` and the bottoms use it
again.  Doing it once at a shift is what made the residual computation
three rewrites instead of three proofs.

**Two mechanical traps, each of which cost a cycle.**
* `VExpr.instSeq`/`Expr.instSeq` use *descending* cuts with `t - 1`, so
  `nP - 1 + 1 = nP` fails at `nP = 0`.  `instSeq_len_succ` /
  `instSeqV_len_succ` handle it (empty argument list, both sides are
  the identity).  Do not case-split on `nP` at every site.
* A lemma stated at depth `d + nP + c` will not `rw` against a goal at
  depth `d + nP`, defeq or not.  Give such lemmas an explicit depth
  parameter plus `(hdd : dd = d + nP + c)`; the same for `instSeq`'s
  cut (`ht : t = c + nP - 1`).

#### 14.7.3 Retraction: `denote_instLevels` already existed

This run first wrote `denote_instLevels` and its two literal helpers
into `Rename.lean`, transposed from `interp_instLevels`.  **All three
already existed** in `Setlec/TTVerify/Extend.lean` (`ValParams`,
`natLitT_params`, `strLitT_params`), where the delta step had needed
them; `lake build`'s duplicate-name error is what caught it.

§0's practice says: before designing a bridge lemma, look for its
set-model counterpart.  The miss says the practice has a **second
half**: *search this side too*.  The set-model counterpart's existence
tells you the statement is right; it tells you nothing about whether
the bridge already has it.

What the retraction does **not** touch: `denote_renameConsts` really
has no counterpart on this side, and `RenEqT`/`PiDomsRenEqT` really are
stranded in `Model/TeleElim.lean`.

#### 14.7.4 GRANTED (#135, form 1): the equation's type slot needs its sort

**Form (1) landed 2026-08-27.**  `checkEtaThmF` / `checkUnitThmF` (and
their `Env` mirrors in `Modeled.lean`) now require
`tbodyM == Expr.sort ℓA`; `EtaPins` carries `tbodyM = Expr.sort ℓA` as
the last conjunct of each half, and `checkEtaThm_inv` /
`checkUnitThm_inv` forward it.  That is the supplier for every
`StatementSortPin` site — `UnitFoldTT`'s and `EtaFoldTT`'s — and
`tbody = Expr.sort l` is the definition verbatim, so the swap is
`exact` at the site.  See DESIGN.md, "The capability checks pin the
model type's sort".

**Still open, and deliberately out of #135's landing scope** (the grant
was form (1) only): form (2), the semantic `checkIotaSidesTy` check,
which is what the `IndBottom*TT` / `ProjBottomTT` obligations need for
*their* sort premise.  §14.7.7's second eta premise is *not* on that
list any more — §14.7.8 retracts it; its supplier has existed since
task #71 and no checker change is owed.  §14.7.7's closing sentence
stands either way: form (1) is unaffected by the resizing.

The rest of this section is the original request, kept for the
reasoning.

**The obligation.**  Every one of `DeclIndTT`'s five obligations ends
at `Deq.ofEqThm`, which calls `EnvTT.eq_law`, which fires `eqValT`'s
three β-steps.  `eqValT ψ = .lam (.sort (ψ uNT)) …`, so the *first*
β-step's premise is

    Δ ⊢ Â : Sort (ψ₂ uNT),   ψ₂ uNT = ⟦ℓA⟧

where `Â` is the equation's type slot and `ℓA` is the level the
statement's `Eq.{ℓA}` carries.  The other two premises are the two
sides' typings, which the pins and the use site already give.

**Why it is not derivable.**  The set model gets the corresponding
membership from `AnnotOk` (`unit_rule_fold`'s `hαu`, via
`lam_dom_of_ne`), and this bridge dropped `AnnotOk` by design (§2).
Its natural replacement — inverting the theorem's own derivation —
**cannot** work: recovering `Â : Sort ⟦ℓA⟧` from
`⊢ h : Eq.{ℓA} Â a b` means inverting `HasType.app` down to
`⊢ eqValT : Π (Sort ⟦ℓA⟧) …` and reading the domain back off, which is
Π-injectivity, which `propext` **refutes**
(`Setlec/TTVerify/Inversion.lean`).  A "stored types are types"
invariant would not help either, for the same reason: it gives
`Â : Sort u` at *some* `u`, and `u = ⟦ℓA⟧` is exactly the step
injectivity would have to license.

Nor is the level pinned anywhere: `checkUnitThm` binds the equation's
level as `_ℓ` and the model type's telescope residual as `_`, and
compares **neither** — §0's third tell (a conjunct the code computes
and discards), read off the checker rather than off a proof.

**What is being asked for.**  One additional check, in two forms:

1. *Syntactic*, for `checkUnitThm` / `checkEtaThm` (both are `Bool`,
   with no `ops` in scope): require the model former's telescope
   residual to be the equation's sort — `tbodyM == Expr.sort ℓA`, or
   more robustly `tbodyM` is `.sort ℓM` with `Level.isEquiv ℓM ℓA`,
   using the checker's own level equivalence rather than syntactic
   equality.  `EtaPins` gains the conjunct; `checkUnitThm_inv` /
   `checkEtaThm_inv` forward it; the model path is unaffected (it
   gains an unused fact).
2. *Semantic*, for `checkIotaSidesTy`, which already has `ops` and
   already certifies that both sides inhabit `alphaS`: additionally
   infer `alphaS`'s type and `isDefEq` it against `.sort ℓ` at the
   equation's level.  This is the same shape as the certificates task
   #129 and #130 added, and for the same reason.

**Why the recommendation is (1)+(2) rather than a workaround.**  With
(1) the bridge derives the semantic fact in four lines, from
`EnvTT.has_type` at `T._model` plus a *second* application of
`teleAlign_of_stripPis` — the spine lemma paying twice, which is a good
sign about the shape.  Without it there is no supplier at all: the
premise is not weakenable (`HasType.beta` reads the λ's own
annotation), `EqLawTT` is not restatable without it (there is no
cumulativity rule), and choosing a different `ψ` is blocked by
`val_params`.

**The risk, priced — measured, not argued.**  Whether the real
preprocessor emits `T._model : ∀ p⃗, Sort ℓ` with the *same* level
expression the eta and unitlike theorems carry is an empirical
question (the generator takes the theorem's level from
`Meta.getLevel` on the carrier, `lean-inductive-models`,
`Driver/Unitlike.lean` — it should agree, but level normalisation
could differ).  §0's second practice says to count it in the real
stream rather than assume, and a property nobody can check casually is
one nobody will check — so it was checked.

`checkEtaThmF` / `checkUnitThmF` (the **`FEnv` path**, which is the one
that executes — the `Env` versions in `Modeled.lean` are never reached
at runtime, and probing them first produced zero hits on a 3 653-
declaration stream) were instrumented to report
`tbodyM == Expr.sort ℓA` at every call, and the whole fixture corpus
run:

| corpus | eta hits | unit hits | `==` holds |
|---|---|---|---|
| `_tmp/arena-tests` (182 streams, incl. `init-prelude`) | 300 | 47 | **347 / 347** |
| `tests/e2e` (all fixtures, incl. gzipped) | 678 | 44 | **722 / 722** |

**1 069 calls, zero counterexamples.**  The plain `==` form is
sufficient; the `Level.isEquiv` form is the fallback if a future
preprocessor normalises differently, and costs nothing to prefer.  The
instrumentation was temporary and is not committed (the checker files
are untouched: `git status` clean, gates re-run green after revert).

**Until it is granted**, `UnitFoldTT` carries the fact as the
hypothesis `hTmSort : tbodyM = Expr.sort ℓA`, isolated to one line
precisely so that a different supplier can be swapped in without
touching the proof, and `DeclIndTT` cannot discharge it.

#### 14.7.5 A hypothesis dropped, and why that is the honest move

`UnitFoldTT` does **not** take the unitlike theorem's `find?` fact.
The proof never reads it: `unit_rule_fold` needs the lookup for
`interpClosed_extend_fresh`, while the bridge's `denote_depth_closed`
needs only `hasFvar = false` and `looseBVarsBounded 0`.  The linter
found it (`Variable name 'hthmE' is not explicitly referenced`), and it
was dropped rather than `_`-prefixed.

This is §8.2's rule applied to a hypothesis *copied in from the model*
rather than invented: transposing the model's statement is the default,
but a premise the transposed proof does not read is a claim about the
contract that is not true.  The fold's contract is the pinned type
shape plus inhabitation, and nothing about which constant carries it.

#### 14.7.6 Status

* **Done**: the phase's shared machinery (§14.7.2), `UnitFoldTT` and
  `EtaFoldTT`.
* **Blocked on §14.7.4** (task #135, in flight): both folds' discharge
  of `StatementSortPin`.
* **Blocked on §14.7.7** (filed, not granted): `EtaFoldTT`'s discharge
  of `EtaRhsTyped`.
* **Next**: the two bottoms, then `ProjBottomTT`, then `CheckDeclTT`.
  Their type slots are motive applications rather than the model
  former, so they meet §14.7.4 at a *different* `Â` and will want
  form 2 (the `checkIotaSidesTy` route) rather than `StatementSortPin`;
  their two sides are already certified.

**The prediction of §14.7.2 cashed.**  `denote_paramTuple` /
`instSeq_paramTuple` were factored out of `UnitFoldTT` on the argument
that every pinned domain is the same tuple at a shift.  `EtaFoldTT`'s
residual — which has a *nested* spine, the fabricated constructor over
`etaFields` projection applications — is `denote_paramSpine` four times
and `instSeq_paramList` three times, and `denote_etaResidual` went
through on its first compile.  That is the payoff of the factoring
stated as an outcome rather than as a plan.
#### 14.7.7 The premise is one of *three*, and eta needs a second one

Found while starting `EtaFoldTT`, on the grant to proceed.  **This is
not a new gap; it is the same gap, correctly sized** — and it changes
what task #135 should deliver, so it is recorded before the eta fold
is written rather than after.

**The root cause, restated.**  What the bridge lost with `AnnotOk` is
not "a sort fact".  `annotOk_spine_inv` inverts the *whole* equation
spine and `lam_dom_of_ne` reads back **all three** of its arguments'
memberships — `vα ∈ˢ univ ⟦ℓ⟧`, `vl ∈ˢ vα`, `vr ∈ˢ vα`.  That is
exactly what `EqLawTT` needs, because `eqValT` is a three-λ tower and
`HasType.beta` reads each λ's own annotation:

| obligation | `⊢ Â : Sort ⟦ℓ⟧` | `⊢ lhs : Â` | `⊢ rhs : Â` |
|---|---|---|---|
| `UnitFoldTT` | **missing** (#135) | law premise `hB` | law premise `hB'` |
| `EtaFoldTT` | **missing** (#135) | law premise `hB` | **missing** — the *fabricated* constructor spine |
| `IndBottom*TT`, `ProjBottomTT` | **missing** (#135) | `checkIotaSidesTy` ✓ | `checkIotaSidesTy` ✓ |

So the four obligations owe between one and two of the same three
facts, and which ones they owe is an accident of what each law happens
to quantify over.

**The precedent settles the shape of the ask.**  `checkIotaSidesTy`
exists for *precisely* this reason — task #100 stage 3, and its
docstring says so: "the collapse removed value-driven domain pinning,
so the fold derivation reads these certificates".  The iota half of the
job was done once already.  `checkEtaThm`/`checkUnitThm` never got the
same treatment because on the model side `AnnotOk` was still covering
them.  **#135 is the eta/unit half of a job the project has already
done on the iota half**, and it should be scoped to the same facts, not
to the sort alone.

**Why eta's right-hand side is not derivable either.**  Same wall:
recovering `⊢ rhs : Â` from `⊢ p : Eq.{ℓ} Â B rhs` means inverting the
application chain down to `eqValT`'s λ and reading its domain back,
which is Π-injectivity, refuted.  And it is worth naming why the fact
*looks* free: `⊢ rhs : Â` is a **consequence** of the very `Deq` the
fold is proving (`Deq Δ B rhs` plus `⊢ B : Â` gives it by `conv`).  It
is equivalent to the goal, not weaker than it — which is exactly why no
amount of rearranging the fold produces it.

> **RETRACTED in §14.7.8**: the paragraph below claimed the checker
> does not certify the fabricated spine and that one `iotaCertsI` call
> was missing.  **It does certify it**, at the caller.  The premise is
> still owed by `EtaLawTT` — the re-signing stands — but *no checker
> change is needed for it*.  Read §14.7.8 before acting on this.

**Recommended supplier, and why it is a separate grant.**  Unlike
#135's conjunct there is no syntactic pin that gives it: the
fabrication's typing is semantic.  The cheapest faithful route is a
*third premise on `EtaLawTT`*, supplied by the consumer:

    HasType Δ (VExpr.mkAppN (cval caps.etaCtor ψC) (xs ++ projs))
      (VExpr.mkAppN (cval T ψ) xs)

The consumer can nearly supply it already.  At the rescue site
`structEtaCertWithI` (`Setlec/Kernel/CoreI.lean:1063`) runs
`iotaCertsI` on `T`'s parameter telescope at `targs`, and
`structEtaProjCertsI` runs `iotaCertsI` on **each projection's**
telescope at `targs ++ [b]` — so every field application is already
certified at its own residual.  What is missing is one more
`iotaCertsI`, on the **constructor's** telescope at `targs ++ projs`;
with it, `TeleTyped.appN` gives the fabrication's typing directly.

That is a landed-invariant re-signing (`EtaLawTT`, hence `CapsOkTT`,
hence `eta_rescue`'s call) plus one checker call, so it is **not** in
the standing grant and is filed here as a request rather than acted on.
It is additive to #135: form 1's syntactic conjunct is exactly right
and unaffected.

**Until then**, `EtaFoldTT` will carry both premises as named
hypotheses beside `StatementSortPin`, so that each has one supplier and
one swap.
#### 14.7.8 RETRACTION: the synthetic-spine certificate exists

§14.7.7 said the checker never certifies the fabricated constructor
spine and that the fix was "one more `iotaCertsI`, on the
constructor's telescope".  **That is wrong**, and the record caught it:
it contradicted the predecessor's `structEtaCertStepTT` report, which
had recorded as a *measured overshoot* that `structEtaCertWith`
supplies more than predicted, naming task #71's synthetic-spine
certification.  Two careful reports disagreed about one site; the
disagreement was the signal.

**What is actually there.**  The call is at the **caller**, not inside
`structEtaCertWithI`:

```
-- Setlec/Kernel/CoreI.lean, majorToCtorI's eta branch (~1246)
-- synthetic-spine certification, as in the K branch (task #71)
let tyCtor ← constTyAtM fe ctorI rl.ctor ust
if ← iotaCertsI r fe depth tyCtor (margs ++ projs) then do
  if ← structEtaCertWithI r fe depth fab major tmaj then …
```

I read `structEtaCertWithI`'s body, found `iotaCertsI` only on `T`'s
telescope and on the projections, and concluded the constructor's was
missing.  It is two lines above the call.  **And the bridge already
inverts it**: `Setlec/TTVerify/MajorStep.lean`'s `fab_reduct` takes
`hcerts : iotaCertsP … cvj.type … L = .ok true` and runs `certs_typed`
on it — then uses only `hfit.spine`, the `DenoteSpine`, and discards
the *typing* half.  §0's third tell, in the bridge's own code: a
conjunct available at the only use site and declined.

So **no checker change is needed at this call site** for the fabricated
spine, and the request that would have become #136 is withdrawn.
(**§14.7.10 amends the scope of this sentence**: `structEtaCertWith`
has a *second* caller, reached from `defeq`, which is not so guarded.
The fact recorded here stands; the conclusion "no checker change is
owed for this premise" was drawn from one call site and is too
strong.)  The `EtaLawTT`
re-signing still stands — the field must *ask* for the premise — but
its supplier is a certificate that has been there since task #71.
(The number was reused: task #136 is §14.7.9's *different* request,
the constructor-residual pin, and it landed.)

**The generalisable lesson, because it is not "look harder".**  A
guard can live at the caller and still be part of the callee's
contract.  Reading a function body is not reading its *precondition*;
the checker composes its certificates by sequencing, so the question
"is X certified?" has to be asked of the **call site**, not of the
definition.  The predecessor's report was phrased about the site
("`structEtaCertWith` supplies…"), mine about the definition, and only
one of those is the thing the fold consumes.

**Where the remaining link actually is, stated without repeating the
error.**  The certificate yields `⊢ fab : ⟦rest⟧` where `rest` is the
*constructor's* telescope residual; the law's premise wants
`⊢ fab : T p⃗`.  Closing that needs "a stored constructor's result type
is its family applied to the parameters".  That fact **is** checked —
on the **direct** path, `checkDirectCtor`
(`Setlec/Kernel/Checker.lean:125`, `cbody == directFam …`, plus the
opened-residual check at :143) — and I have **not** found it on the
modeled path, which is the one `EtaFoldTT` serves.

That is deliberately stated as "not found", not as "missing".  The
whole point of this section is that the second reading is what costs.
Before any request: check whether `checkMemberVal`'s `eqUpToNames`
against the model constructor, or `EtaPins`' constructor-model
conjuncts, already deliver it — and if a request is still warranted,
price it with the same corpus measurement §14.7.4 used.
#### 14.7.9 GRANTED, but read §14.7.11 first (task #136)

**The site and the subject named below are wrong**, and §14.7.11 is
this section's own retraction: the request was measured on
`indBlockCapsF`'s **raw** `cvC.type` and specified against the
constructor's **stored** `ConstantVal` — two different objects.  What
landed 2026-08-27 is the §14.7.11 form: `ctorResidualOk`, on the
stored constant, guarded by `caps.eta`, in `checkIndDecl`'s
single-constructor branch (and its two driver mirrors).  The
re-measurement — including raw vs stored side by side, which never
disagree in 1356 blocks — and the one deviation from §14.7.11's letter
(the check runs one step after the member install, because
`checkIndMember` has no `T` in scope) are in `DESIGN.md`, "The eta
capability pins the constructor's residual".

The verify-side carrier is *not* `EtaPins` (§14.7.11(b) confirms the
category error the implementer diagnosed); it is the `EnvTT` field
discharged from the install's own inline inversion, and that work is
not part of #136's landing.  The rest of this section is the original
request, kept for the reasoning — with its object named loosely, which
is exactly what §14.7.11 is about.

§14.7.8 left one question open and told its author to read before
requesting.  Read, then measured; here is the outcome.

**The reading.**  `checkMemberVal` (`Setlec/Kernel/Modeled.lean:361`)
checks, for *every* block member including constructors,
`eqUpToNames (cvA.type.renameConsts f) cvm.type` — so the public
constructor's type is tied to the model constructor's.  `EtaPins`'
constructor-model conjunct gives only `find?` and `levelParams`, not a
shape.  So the chain public → model terminates at the **model**
constructor's residual, which nothing pins: models are stored opaque
(`DESIGN.md`, "modeled inductives are stored opaque").  The
`eqUpToNames` transport is real but has nothing to transport *from*.

The fact is available on the **direct** path — `checkDirectCtor`
(`Setlec/Kernel/Checker.lean:125`) requires the constructor's residual
to be `directFam T lps nP nF`, and re-checks it opened at :143 — and
has no counterpart on the modeled path.

**The measurement, because §14.7.8's own rule applies to its author.**
`indBlockCapsF` is where the data lives (`cvT`, `cvC`, `nP`, `nF` all
in scope), so it was instrumented to report, per modeled block, both
capability verdicts and whether the public constructor's residual is
`directFam`.  Whole corpus, arena + e2e:

| `eta` | `unitlike` | residual is `directFam` | blocks |
|---|---|---|---|
| true | false | **true** | 959 |
| true | true | **true** | 19 |
| false | true | **true** | 72 |
| false | false | true | 228 |
| false | false | **false** | 99 |

**978 / 978 eta-capable blocks and 91 / 91 unit-capable blocks satisfy
it; every one of the 99 failures is a block with neither capability.**
The failures are exactly the *indexed* families — `Acc`, `HEq`,
`Int.NonNeg`, `IndexedSingleton`, `SortElimProp`, … — whose
constructor residual is `T p⃗ i⃗` and which never earn eta or unit.
So an *unguarded* check would reject real streams (99 sites), and a
check *guarded on the capability* rejects nothing.

**The request, therefore, is one conjunct on `indBlockCapsF`'s `eta`
field** — where `cvC` is already in scope, unlike `checkEtaThmF` —
requiring the constructor's residual to be `directFam cvT.name
cvT.levelParams nP nF`: literally the conjunct `checkDirectCtor`
already makes, moved to the modeled path and guarded by the
capability.  `unitlike` does not need it (its right-hand side is a law
premise, not a fabrication).

With it, `eta_rescue` discharges `EtaLawTT`'s new third premise from
the task #71 certificate `MajorStep.lean` already inverts: that gives
the fabrication at the *constructor's* residual, and the conjunct is
what identifies that residual with `T p⃗`.

**The spelling is committed in advance, for the implementer to grep.**
`Setlec/TTVerify/DeclInd.lean` now carries

```lean
def CtorResidualPin (T : Name) (lps : List Name) (cvC : ConstantVal)
    (nP nF : Nat) : Prop :=
  ∃ bs, cvC.type.stripPis (nP + nF) = some (bs, directFam T lps nP nF)
```

next to `StatementSortPin`, and for the same reason: a conjunct stated
in the shape the bridge consumes makes the swap `exact`, and one
stated in any other shape makes it a shim (§0's first tell).  Three
things are load-bearing in it — `stripPis` at the **full** telescope
`nP + nF`, the binder list **unconstrained**, and `directFam`'s last
argument `nF` (the field count, as in `checkDirectCtor`'s call, *not*
the `0` a recursor's major premise uses).  It is stated over the
**public** constructor's stored `ConstantVal` because the model side
cannot serve it — a model's own residual is unpinned, which is what
the reading above established.

**And note what the measurement bought beyond a yes/no.**  The naive
form of this check was *wrong* — 99 counterexamples — and the guard
that fixes it is not something reading the code would have suggested,
because the code has no place where "eta-capable" and "constructor
residual" are looked at together.  §0's second practice earning its
keep: the suite would have gone green on a guarded check and red on an
unguarded one, and only counting told which.
#### 14.7.10 AMENDMENT to §14.7.8: `structEtaCertWith` has two callers

§14.7.8 established a *fact* — `majorToCtorI`'s eta branch runs
`iotaCertsI` on the constructor's telescope (task #71) — and drew a
*conclusion* from it: "no checker change is owed for this premise".
**The fact stands; the conclusion was too strong.**  It is owed, at the
*other* caller.

`structEtaCertWithI` is called from two places
(`Setlec/Kernel/CoreI.lean`):

| caller | line | constructor telescope certified? |
|---|---|---|
| `majorToCtorI`, eta rescue | 1251 | **yes** — `iotaCertsI … tyCtor (margs ++ projs)` at 1248 |
| `structEtaCertI`, from `defeq` | 1111 | **no** — it only does `infer b`, `whnf`, then calls |

and `structEtaCertI` is itself reached from `defeq` twice (1163, 1164,
the symmetric pair).  So the guard §14.7.8 found protects one consumer
and not the other.

The bridge sees it directly: `structEtaCertWith_stepTT`
(`Setlec/TTVerify/StructEtaCertStep.lean`) carries `hbT : HasType Δ vb W`
— the *stuck subject's* typing — and **no typing of the fabrication**,
and its header states the certificate is "self-sufficient: … so
everything `EtaLawTT` asks for is certified on the spot".  That claim
is exactly true of the *current* `EtaLawTT` and becomes false the
moment the law gains the right-hand-side premise.  A landed docstring
that goes stale under a re-signing is the re-signing telling you which
consumer it breaks.

**The error, named, because it is §14.7.8's own lesson committed one
level up.**  §14.7.8 says: ask "is X certified?" of the *call site*,
not of the definition.  I asked *a* call site — the one I had just
been shown — and generalised to "the premise".  The rule needs its
plural: ask it of **every** call site, because a function with two
callers can be guarded by one of them.  `grep` for the callee, not just
for the guard.

**What this asks of #136.**  Nothing — #136 is the
`CtorResidualPin` conjunct, is correctly scoped, and is unaffected.
This is a *separate* one-line checker change, and it belongs inside
`structEtaCertWithI` rather than at its callers, precisely so that
both consumers are served:

```
-- after structEtaProjCertsI, where `projs` is already in scope (:1093)
let tyCtor ← constTyAtM fe c cn us
if ← iotaCertsI r fe depth tyCtor (targs ++ projs) then …
```

It makes `majorToCtorI`'s copy redundant (harmless, and it can stay).
It can only make the checker *stricter*, so the thing to price is
whether any accepted stream stops being accepted — measurable exactly
as §14.7.4 and §14.7.9 were, and the prior is good, since the same
certificate already succeeds at every `majorToCtor` eta rescue in the
corpus.

**Until it exists**, the `EtaLawTT` re-signing can be threaded but not
completed: `MajorStep.lean`'s consumer discharges the new premise
(certificate + `CtorResidualPin`), and `StructEtaCertStep.lean`'s
cannot.  The re-signing should therefore land *with* it, not before.

## 15. The bottoms: §8.2's sixth narrowing, cashed with its supplier

Scouted before writing either bottom, on the same discipline §14.7.8
extracted: ask the *call sites* what they certify, and ask **all** of
them.

### 15.1 The prediction, and what the reading found

§8.2 predicted a sixth narrowing (after the level and parameter ones)
and `DESIGN.md` §14.6.2 predicted that its plumbing *is* the bottoms'
spine lemma — the thing that moves the constructor spine between the
rule's description of it (`ruleLhsAux`, index slots filled with the
constructor's canonical tuple) and the fired redex's (index slots
free).  Both hold, and there is a third fact the record did not have:
**the guard already exists**, so unlike §14.7.4/§14.7.9 this narrowing
costs no checker change.

`iotaRec` (`Setlec/Kernel/Core.lean`, ~1299), after both `iotaCerts`
and before it will fire:

```
match (cvj.type.instantiateLevelParams …).stripPis (ctorParams + nfields),
      piResidual (cvj.type.instantiateLevelParams …) margs with
| some (_, cbody), some residual =>
  match cbody.getAppFn with
  | .const _ _ =>
    if ← defEqList r env depth
        (residual.getAppArgs.drop rl.ctorParams)   -- canonical indices
        ((args.take mI).drop rP) then …            -- the redex's indices
```

with its own comment: *"the model's iota equation only speaks about
the canonical indices"*.  So a fired redex's index arguments are never
free — they are definitionally the constructor's canonical tuple.
That is the sixth narrowing, in the checker, with a supplier.

### 15.2 `IotaIndexPin`, and why the anticipated piece is not needed

The premise is named now, in the shape the supplier produces, for the
reason `StatementSortPin` (#135) and `CtorResidualPin` (#136) were:
a premise written as the consumer will hand it over discharges by
`exact`; written any other way it needs a shim (§0's first tell).

```lean
def IotaIndexPin (Δ : List VExpr) (restC : VExpr) (cnP mI rP : Nat)
    (xs : List VExpr) : Prop :=
  ∃ (H : VExpr) (cargs : List VExpr),
    restC = VExpr.mkAppN H cargs ∧
    ∀ i, i < mI - rP →
      Deq Δ (cargs.getD (cnP + i) default) (xs.getD (rP + i) default)
```

§14.6.2 budgeted "a `VExpr`-level `getAppArgs` (none exists) or a
reformulation through `restC`".  **The reformulation wins outright, and
the anticipated piece is not built**: the constructor's residual is
already a bound variable of `RecRulesTT` (`VTeleTyped Δ TVj ys restC`),
and `denote_mkAppN_inv` — the bridge's only way of reading a spine
apart — *produces exactly this existential*.  A `VExpr.getAppArgs`
would have to be defined, given lemmas, and then related back to
`mkAppN`; the existential is what the inversion already hands over.

That is a budgeted piece coming in at **zero**, and it is worth the
sentence: the pattern §14.6.2 used to predict it ("the shared piece is
always the spine-mover between two descriptions of a telescope") was
right about *what* was needed and wrong about *what it would cost*,
because it did not notice the mover was already the inversion's output
shape.

### 15.3 What this asks for, and what it does not

* **No checker change.**  Unlike the sort pin (#135) and the
  constructor residual (#136), the guard is there.
* **A `RecRulesTT` re-signing** — one premise, in the fired form's
  established pattern, alongside the level and parameter narrowings it
  joins.  Producers (`DeclBasisTT`'s six blocks) are only *helped*: a
  new premise is a new hypothesis they may ignore.  The consumer
  (`Setlec/TTVerify/IotaStep.lean`) must supply it, and the guard above
  is what it supplies it from.
* The bottoms then meet §14.7.4's sort gap at a **motive application**
  rather than the model former, so they want form 2 (the
  `checkIotaSidesTy` route) as §14.7.6 pre-split — and their two
  *sides* are already certified there, which is the half #135 did not
  have to provide.
### 15.4 The narrowing scoreboard, and the re-signing's validated plan

**Scoreboard.**  Of §8.2's six predicted narrowings:

| # | narrowing | outcome |
|---|---|---|
| 1–3 | levels, parameters, **indices** | **guard already in the checker**; the bridge only certifies it was load-bearing |
| 4 | `Quot`'s parameter narrowing | fatal-and-threaded — the laws are unprovable without it |
| 5 | the equation type slot's **sort** | checker change (#135, landed) |
| 6 | the constructor **residual** + the defeq-path **certificate** | checker changes (#136, #137, in flight) |

The rule stands with a corollary now attached:

> Wherever the model states a law over a hard-coded canonical form and
> the bridge quantifies, the difference is a **checker guard** — and
> sometimes the guard is already there, and the bridge merely
> discovers it was load-bearing.

**On the alignment tally (§8.4): deliberate, or coincidence?**  The
index guard's own comment says *"the model's iota equation only speaks
about the canonical indices"* — so its author added it **for the model
path's benefit**, knowing the law was stated at the canonical form.
That makes it *deliberate forward provision*, not luck: the bridge
inherits it because both verifications need the same fact for the same
reason.  By contrast, `denote_mkAppN_inv`'s output shape *being* the
existential `IotaIndexPin` wants is undesigned — the inversion was
written to read redexes apart, long before anything needed a
constructor residual's index tuple.  One of each, and the distinction
is worth keeping: the first predicts more such guards exist, the second
does not.

**The threading plan, validated by doing it and then reverting.**  The
re-signing was threaded end to end far enough to confirm every link,
then rolled back rather than left half-applied.  What it costs, in
order:

1. `RecRulesTT` gains `IotaIndexPin Δ restC (RecRule.ctorParams rl) mI rP xs`
   after the parameter narrowing.  (`IotaIndexPin` is already placed
   *before* `RecRulesTT` for this.)
2. Two transports take it verbatim: `RecRulesTT.cons`'s `hhead`
   (`Extend.lean` ~1222 and its `intro`/`exact` pair) and `EnvTT.cons`'s
   `hheadRec` (~1442), plus `EnvTT.consBasis`'s (`DeclBasis.lean` ~188).
   **Confirmed compiling.**
3. The six basis blocks then get the conjunct offered; `-`-sweep them so
   it is visibly declined.
4. The single consumer `rec_rules_fire` (`Iota.lean`) assembles it.
5. `IotaStep.lean` supplies its hypothesis, mirroring `hparP` exactly.

**Two more discarded conjuncts, found in step 4 and worth their own
line** — §0's third tell, twice more, in our own code:

* `rec_rules_fire` writes `obtain ⟨RVC, hvC, -⟩ := hfitC.toV hcl hiC`.
  The `-` is `denote … restC = some RVC` — precisely the fact needed to
  read the constructor residual's spine apart.
* `iotaRec_inv` (`Setlec/Verify/InferLemmas.lean` ~726) already returns
  both `piResidual … = some residual` **and** the index `defEqListP`;
  `IotaStep.lean` destructures past them.

So step 4/5's inputs are all present and merely unclaimed — the same
shape as `MajorStep.lean`'s `fab_reduct` discarding `certs_typed`'s
typing half (§14.7.8).  **Three independent instances now**: when this
bridge needs a fact, the first place to look is the conjunct its own
inversion already returns.

**Landed from the attempt** (kept because reusable and green):
`TeleTyped.rest_eq` — a typed walk's residual is `piResidual`'s, the
link between a checker guard stated about `piResidual` and a bridge
that holds the walk.  It is what step 4 needs and nothing else
supplied.
#### 14.7.11 RULING on #136: the checked object is the *stored* type

The #136 implementer refused the verify-side threading for cause and
asked three questions.  Answering them exposed an error of mine, so
that comes first.

**My error, owned.**  §14.7.9 said "`indBlockCapsF` is where the data
lives" and measured `cvC.type` there — the **raw, pre-install**
constructor type.  `CtorResidualPin`'s docstring says the fact is about
"the **public** constructor's *stored* `ConstantVal`".  Those are two
different syntactic objects, and I did not notice I had measured one
and specified the other.  It is the same family as §14.7.8's error:
a fact is about an object, and naming the object loosely is how the
wrong one gets checked.  **The measurement must be redone.**

**(a) Which object.**  The **stored (annotated)** type, decisively, and
not because the raw→stored bridge is hard but because the raw fact is
*not the fact*:

* the environment contains only the annotated constant
  (`checkMemberVal` stores `checkConstantVal`'s output);
* the fire-site certificate reads exactly that (`constTyAtM fe ctorI
  rl.ctor ust`), and so does everything else the bridge has —
  `EnvWF`, `has_type`, `denote_declType`;
* the raw type is *never in the environment*, so no bridge lemma can
  be avoided by choosing it — only added.

The alternative (check raw, prove annotation preserves the `stripPis`
residual as a `directFam` spine) buys nothing and costs a lemma over
cod annotations, #85's pending `Level.simplify` and #117's four
survivors — a real risk surface, standing between a check and a fact
that could simply *be* the check.  Worse, it is a lemma that can
silently rot when annotation changes.  **Check what the consumer
reads.**

`CtorResidualPin`'s *shape* is unaffected — `stripPis (nP + nF)` with
residual `directFam T lps nP nF` — only its subject moves to the
stored `ConstantVal`.

**(b) The carrier: not `EtaPins`.**  The implementer's three failed
spellings are the evidence, and they are diagnosing a category error
rather than a plumbing difficulty: `EtaPins`' parameters reach only
*model-side* constants, and this is a fact about the **public**
constructor.  It does not belong there and should not be forced there
at 37 sites.

The carrier is the approved `EnvTT` field (§14.7.6's design), whose
head obligation is discharged at the member install — where the
annotated `cvA` is *created*, `caps` is in scope (so the capability
guard is expressible as `ci.name == caps.etaCtor && caps.eta`), and
`DeclIndTT` inverts the actual checker run inline.  That also dissolves
the "no named caps inversion exists" objection: the field's obligation
is discharged from the install's own inline inversion, which is exactly
where both sites already invert `indBlockCaps`.

So the check moves with its subject: from `indBlockCapsF` to the
constructor's member install.

**(c) Do not land `0ba1adb` as-is.**  Its conjunct pins a fact the
bridge cannot consume, at a cost that would have to be paid twice.
What carries over unchanged: the byte-identity harness, the negation
probe, the +0.021% measurement, and the placement finding (middle eta
conjunct, so both inline inversions keep `hcape.2`).

**The re-measurement, and one thing to add to it.**  Same cross-tab as
§14.7.9 — capability × property — at the new site.  And since
instrumenting there has both types in hand, **report raw vs annotated
side by side**.  If they never differ on this residual, that is free
evidence about the annotate-shape question; if they do, it is the
counterexample that proves the ruling was necessary.  Either way it
costs one extra field in the trace line.
#### 14.7.12 #137 landed: two certificate instances, and the `inv` is ours

Recorded at the merge, so the re-signing increment does not re-derive
it.  Master `2970b7d`.

**What landed.**  `structEtaCertWithI` / `structEtaCertWith` now run
the constructor-telescope `iotaCerts` themselves, so both callers are
served — the gap §14.7.10 identified at the `defeq` path.  Measured
before landing, as ordered: **1 644 defeq-path evaluations, zero
failures**, cost inside run-to-run spread.  The memoisation prior was
*refuted the useful way* — everything the new certificate re-derives
was already cached, which is why a certificate that looks like real
work costs nothing.

**Two facts the re-signing needs.**

1. **`structEtaCertWith_inv` was deliberately left unchanged.**  It
   steps over the new certificate, so the existential's new conjunct —
   and the destructuring fallout at its existing use sites — belongs to
   *this* increment.  That is the right ownership call (§14.7.10 named
   the consumer; the consumer's inversion is the consumer's), and it
   means the re-signing's step-4 work now has two halves: add the
   conjunct to the `inv`, then consume it.

2. **The caller-side copy at `majorToCtorI` is kept, non-redundantly.**
   Same certificate, *different control flow*: a callee-side failure
   falls through to the `etaFields = 0` `proofIrrel` rescue, while a
   caller-side failure returns the stuck major.  So they are distinct
   *instances* of provably the same call, and the two bridge consumers
   discharge from different ones — `StructEtaCertStep.lean` from the
   callee's, `MajorStep.lean` from the caller's.

**Sequencing, updated.**  §14.7.10 concluded "the re-signing should
land *with* it, not before".  It now lands *after*, unblocked: the
`EtaLawTT` re-signing plus the `EnvTT` field is a single increment
whose only remaining external dependency is #136's re-measurement
(§14.7.11) for `CtorResidualPin`'s discharge — and even that blocks
only the *discharge*, not the threading, since `EtaRhsTyped` carries
the premise in the law's own shape meanwhile.


**Outcome (2026-08-27, landed).**  Re-measured at the new site with
both types in the same trace line: 1356 single-constructor modeled
blocks, **975/975 eta-capable and 90/90 unit-capable satisfy the
property**, all 91 failures capability-free and all of them indexed
families, and **raw vs stored disagree 0 times**.  The free evidence
came out clean — which is evidence, not a licence: the landed check
reads the stored constant through `find?`, so the inversion yields
`CtorResidualPin` for the very `ConstantVal` the environment holds and
the bridge's discharge is `exact`.

One deviation from (b)'s letter, with its reason: the check runs *one
step after* the member install, in `checkIndDecl`'s single-constructor
branch, because `checkIndMember` has no family name in scope (`IndCaps`
does not carry `T`) and threading one would touch 121 references across
`Setlec/Model/*` and `Setlec/Verify/*`.  Same value, read back from the
environment; three localised `by_cases` in the Model layer; the fact
handed over is the stronger stored-and-found form.  Details, gates and
the negation probe (decline at `inductive LT`, arena 67/92, e2e 32/67)
are in `DESIGN.md`, "The eta capability pins the constructor's
residual".
#### 14.7.13 #136 landed, and the sentence worth keeping

Master `eef1991`.  With it, **all four named premises of the
`DeclIndTT` phase have landed suppliers**: `StatementSortPin` (#135),
`EtaRhsTyped` (#137), `CtorResidualPin` (#136), and `IotaIndexPin` —
whose supplier was in the checker all along (§15).

**The discharge shape, confirmed against the landed code.**
`ctorResidualOk env' T ctorName lps nP nF eta` is `!eta ||` a
`find?`-then-`stripPis` match whose body is `== directFam T lps nP nF`
— i.e. exactly `CtorResidualPin T lps cvCA nP nF` on the *stored*
`cvCA`, guarded on the capability, with the `find?` conjunct alongside.
That is what §14.7.11's ruling asked for and what a block-install head
obligation wants, so the `EnvTT` field's discharge is `exact` against
the shape fixed in advance.  **Site**: once per single-constructor
modeled block, between the recursor group and the projection-family
freshness check, in all three drivers — *not* inside `checkIndMember`,
where no family name is in scope (threading `T` would have been 46 call
shapes).  Nothing in the fold needs it earlier, so the site stands.

Re-measurement clean: 975/975 eta-capable blocks; the 91 failures are
all capability-free indexed families; **raw vs stored disagreed zero
times**, recorded as evidence and not as a licence — the ruling was
about which object the consumer reads, and that argument does not
depend on the two agreeing.

**The sentence, which is §14.7.11 restated from the implementation
side and belongs in the practices rather than in a task's postmortem:**

> The first attempt passed every gate, byte-identity included, and was
> still checking the wrong object.  **Gates prove a change is inert;
> only naming the object precisely proves it is the right change.**

That is the exact complement of §0's gate note.  The gate note says a
check run against a cache measures the cache; this says a check run
against the wrong object measures nothing at all — and no amount of
green tells you which you have.  Both failures are invisible in the
output and visible only in the *setup*, which is why the setup is what
the record has to carry.
### 15.5 The re-signing, landed — and the sweep's own evidence

`RecRulesTT` now carries `IotaIndexPin`.  The threading was exactly
§15.4's plan; three things it turned up are worth keeping.

**The sweep is evidence, not bookkeeping.**  Seven `hheadRec` sites
discharge `RecRulesTT`'s head obligation across the six basis blocks.
Of them, **five decline the parameter premise with `_` and two consume
it** — and the two are `Quot`'s eliminators, exactly where §8.2
recorded the fifth narrowing as *fatal rather than merely wasteful*
("a field typed at the constructor's parameter cannot be moved to the
recursor's").  A record claim about which blocks need which premise,
confirmed by where the underscores fall.  All seven decline the new
index premise, as expected: the basis recursors are not modeled and
their laws never mention canonical indices.

**Three inversion conjuncts were being discarded, and two of them were
the whole job.**  `IotaStep.lean` destructured `iotaRec_inv` as
`… hcerts, hmcerts, -, -, -, -, rfl⟩`.  The second and fourth `-` are
`piResidual … = some residual` and the index `defEqListP` — precisely
the premise's two ingredients.  Un-discarding them *is* the supplier.
With `fab_reduct`'s discarded typing half (§14.7.8) and `toV`'s
discarded denote fact (§15.4), that is **four** instances now, and the
generalisation has earned its place in §0:

> When this bridge needs a fact, look first at the conjunct its own
> inversion already returns.

**A third "already existed".**  A `defEqListP_length` helper was
written for the bounds, then deleted: `defEqList_inv` already returns
`⟨length, pointwise⟩`, and the neighbouring `hparP` was already using
it that way *twelve lines above the new code*.  After
`denote_instLevels` (§14.7.3) that is the second lemma this run wrote
before searching — and the second time the neighbouring code already
had the answer.  §14.7.3's "search this side too" wants a sharper form:
**read the sibling obligation before writing a helper for yours**; the
two consume the same inversion and will want the same accessors.

**What the premise cost, end to end**: one line in `RecRulesTT`, three
transports (`RecRulesTT.cons`, `EnvTT.cons`, `EnvTT.consBasis`), seven
`_`s, ~60 lines assembling it in `rec_rules_fire` from
`denote_mkAppN_inv`, and ~70 lines supplying it in `IotaStep.lean` —
of which the residual's four frame conditions were most of the work,
and all four were already available (`piResidual_WScoped`,
`piResidual_looseBVars`, `piResidual_fvarLeaves` plus a pointwise
`CtxOk`).  Nothing new about `VExpr` was needed, as §15.2 predicted.
### 15.6 The bottoms' first piece: one opener, not two

`IndBottomPlainTT` scouted.  Its entry kit is `PlainChecked`
(`Setlec/Verify/Extend/Iota.lean:34`) — already `V`-free and already in
`Verify/`, so unlike the folds' `EtaPins` there is nothing to restate.

**The one structural mismatch, and it is now closed.**  Every *iota*
pin is phrased against `openPisAtFvars` (the checked `iota_j`
theorem's telescope opened at free variables, its parts read off with
`getAppFn`/`getAppArgs`), while the capability pins use `stripPis` and
the folds' machinery — `piTower_of_stripPis`, `denote_paramTuple`,
`instSeq_paramTuple` — was built on `Expr.instSeq (openFvars d k)`.
Two openers, one telescope.

`openPisAtFvars_stripPis` is the agreement: a successful
`openPisAtFvars k e d` yields the `stripPis k` the fold machinery
wants, the opening variables at indices `d + j`, and an opened body
`ErasedEq` to the canonical one.  `ErasedEq` is the right tolerance
rather than a weakening: the two openers differ *only* in whether the
opening variable carries the binder's own name and domain or canonical
ones, and `denote` reads neither — so `denote_erasedEq` consumes the
difference exactly.

So the bottoms inherit the folds' machinery instead of getting a second
copy against a second opener.  That is the same economy §14.7.2 named
for `denote_paramTuple`, one level up: **make the two descriptions
meet once, at the opener, rather than per-lemma.**

**A false lemma caught by the `simp` that would not fire.**  The
supporting step wants "if the opened telescope strips, so does the
unopened one".  Stated for a general instantiation it is **false** —
`(.bvar 0).instantiate1 v 0 = v` may be a `∀` while `.bvar 0` is not —
and the proof announced it by leaving the catch-all branch with nothing
to reduce.  Restricted to `fvar` instantiation it is true and is what
the checker actually does; the existing
`stripLams_instantiate1_fvar_isSome_rev` had already made the same
restriction for λ-telescopes, which is confirmation rather than
coincidence.  Recorded because the tell is cheap: **a catch-all branch
where the rewrite makes no progress is often the counterexample, not a
missing simp lemma.**

## 16. HANDOFF: what a successor needs that the files do not say

Written at the end of the run that landed the phase's machinery, both
folds, both re-signings and four pins with suppliers.  Branch
`feat/119-ttverify-stage2`, worktree `.claude/worktrees/ttv-stage2`,
merged `--ff-only` **from the repo root** (a bare merge inside the
worktree reports "Already up to date" and does nothing — verify by
master's SHA, never by the merge's output).  `_tmp/` is per-worktree:
if the `lean-inductive-models` symlink is missing, `arena.sh` reports
53/67 silently.  Gate procedure: §0's forced-recompile note, then
`lake test`, arena 90/92, e2e 67/67, split 11/11, infer-only 5/5,
axioms exactly `[propext, Classical.choice, Quot.sound]`.

### 16.1 `IndBottomPlainTT`, planned

**The entry kit is free.**  `PlainChecked`
(`Setlec/Verify/Extend/Iota.lean:34`) is already `V`-free and already
in `Verify/`, so unlike the folds' `EtaPins` nothing needs restating.
Its destructuring is 21 existentials and 25 conjuncts; **this pattern
is verified to elaborate**, copy it:

```lean
obtain ⟨thmName, cvt, ci, fvs, tbody, lA, alphaS, lhsS, rhsS,
  cdoms, cres, rdoms, rrest, fvsP, restP, cdomsP, crestP, xFvsP,
  crest2, ldoms, lrest,
  hthm, hcvt, hlps, hopen, hheadEq, hargs3, hlhead, hlarity, hlpre,
  hmaj, hCstrip, hcinst, hclen, hdeIdx, hdeFld, hrinst, hdePre,
  hopenP, hcinstP, hdePars, hopenX, hlinst, hdeLam, hdeRhs,
  hlhsTy, hrhsTy⟩ := hkit
obtain ⟨bs, body₀, hstrip, hlenFvs, hidxFvs, herased⟩ :=
  openPisAtFvars_stripPis (rP + cnF) hopen        -- applies directly
```

**Provenance of the model's ~60 hypotheses.**

| bridge source | what it covers |
|---|---|
| `PlainChecked` (free) | the whole syntactic layer: the opener, the `Eq` head/args, the LHS's head/arity/prefix/major, the constructor instantiation and its canonical index tuple, the four `DefEqListOk`s, the RHS defeq, **and the two sides' typings** (`hlhsTy`/`hrhsTy` — `checkIotaSidesTy`, §14.7.7's two "already certified" entries) |
| `openPisAtFvars_stripPis` (new, landed) | turns `hopen` into the `stripPis` that `piTower_of_stripPis`, `denote_paramTuple` and `instSeq_paramTuple` consume; also gives `fvs[j] = .fvar (d+j) _ _` and the `ErasedEq` body |
| `denote_renameConsts` + `RenEqT`/`PiDomsRenEqT` | the public↔`_model` transport, exactly as in `UnitFoldTT` |
| `EnvTT` fields | `has_type` at the theorem, the recursor and the constructor; `eq_law`; `val_params`; `wf` |
| `IotaIndexPin` (landed, in `RecRulesTT`) | the fired redex's indices are the constructor's canonical tuple |
| **genuinely new** | the LHS reassembly, the `Deq` spine congruence, and `αS`'s sort (below) |

**The one thing with no supplier — expect it, it is the next
exception-list item.**  §14.7.7's table says the bottoms owe the *sort*
of the equation's type slot.  Here that slot is `αS`, a **motive
application**, so `StatementSortPin` does not apply and there is no
syntactic pin to be had: `checkIotaSidesTy` certifies both *sides*
inhabit `αS` and says nothing about `αS : Sort ℓA`.  The request is
form 2 of §14.7.4 — extend `checkIotaSidesTy` (it already has `ops`)
with `inferType αS` and an `isDefEq` against `.sort ℓA`.  **Do not ask
before measuring** (§14.7.9): instrument `checkIotaSidesTy`, cross-tab
over arena + e2e, and only then request.  Commit the named `Prop`
first so the implementer can grep it, the way `StatementSortPin` and
`CtorResidualPin` made their swaps `exact`.

**Four hard spots, and what I would try at each.**

1. *`αS`'s sort* — above.  Carry it as a named hypothesis meanwhile;
   the fold is otherwise complete without it.
2. *Indices*: `hdeIdx` relates `(lhsS.getAppArgs.drop rP).take (mI-rP)`
   to `cres.getAppArgs.drop cnP`; `IotaIndexPin` relates the *fired*
   redex's indices to the constructor residual's.  Compose by
   `Deq.trans` — the two speak about the same canonical tuple from the
   install side and the fire side respectively, which is the whole
   point of the sixth narrowing.
3. *Spine congruence*: `Deq.app`/`appFun`/`appArg` exist;
   an n-ary `Deq.mkAppN` does **not**.  Write it (a `List` induction,
   ~10 lines) — the LHS reassembly needs it once per spine.
4. *`hdeRhs` and the four `DefEqListOk`s* need `DefEqClaimsTT` **at the
   install environment**.  This is the structural question to settle
   *first*, before any of the above: the folds never needed the claims
   because they consumed only typings.  Check how `DeclBasisTT`'s
   `RecRulesTT` discharge obtains them (`DeclBasis.lean`'s block
   lemmas) — if the install-time claims are not available, that is a
   design question, not a proof step, and it should be raised before
   the body is written.

### 16.2 `IndBottomNestedTT`: the delta

`NestedChecked` (`Verify/Extend/Iota.lean`, just below `PlainChecked`)
mirrors it *exactly* except for how the major is formed.  So:

* **Verbatim**: the opener bridge, the `Eq` head/args handling, `αS`'s
  sort (same gap), the RHS defeq, the two sides' typings, and — per
  the docstring's own sentence — **the index premises, which "flow
  through exactly as on the plain path"**.  That is the cashed form of
  §14.6.2's "budget one piece, not two".
* **Different**: the major is the constructor at the *stored* level
  instantiations `lvls` and parameter instantiations `pins`, in
  **rP-context** (`Expr.lowerBVars` at install, `Expr.instSpine` at
  the fire site), not at the telescope's variables.  The fire-site
  counterpart is `recFireComparands`'s `.nested` branch, which the
  landed `hlev`/`hpar` premises of `RecRulesTT` already thread.
* Memory note #105 ("nested-aux iota rules") is the design record for
  the pins' rP-context and the index-var split; read it before
  starting, not after.

### 16.3 `ProjBottomTT`, and the `EtaLawTT` + `EnvTT` increment

**`ProjBottomTT`** should be `IndBottomPlainTT` at `cnF = 0`:
`checkProjFn` stores a projection function as a *degenerate recursor*,
so it lands in `RecRulesTT` and **not** in `ProjOkT` — `ProjOkT` is
untouched by `DeclIndTT`.  Do the plain bottom first and see how much
generalises; my expectation is that the entry kit differs and the body
does not.

**The `EnvTT` field, designed but not written.**  Shape, chosen so
that mid-block states are vacuous rather than false:

```lean
def CtorResidualOkT (env : Env) : Prop :=
  ∀ T cvT caps cvC, env.find? T = some (.indInfo cvT caps) →
    caps.eta = true →
    env.find? caps.etaCtor =
      some (.ctorInfo cvC caps.etaParams caps.etaFields) →
    CtorResidualPin T cvT.levelParams cvC caps.etaParams caps.etaFields
```

**Why implication-shaped and not `∃ cvC, …`**: a block stores the
former before the constructor, so an existential form is *false*
mid-block, exactly the way `SameDoms.refl` was false (§0's fifth tell).
The implication is vacuous until the constructor lands and is
discharged when it does.  It also matches the consumer: `eta_rescue`
already holds the constructor's `find?` (from `EtaFamilyStoredT`), so
it can apply the field directly.

**Threading**: `.empty` is trivial; `.cons` is preserved by freshness
(`find?` is monotone) with a head obligation at the constructor's
install.  But note #136's check runs **once per block, after all
members** (between the recursor group and the projection-family
freshness check) — so the natural discharge is at the *block* level in
`DeclIndTT`, not per-`cons`.  Expect to prove the field for the whole
block at once and to thread it unchanged through the member conses.

**The `EtaLawTT` re-signing** is one premise (`EtaRhsTyped`'s body),
both suppliers landed (§14.7.12): `MajorStep.lean`'s consumer from the
caller-side certificate, `StructEtaCertStep.lean`'s from the callee-side
one that #137 added.  `EtaFoldTT` then *drops* `EtaRhsTyped` — the
premise moves from the fold's hypothesis list into the law's binder,
which makes the fold shorter, not longer.

### 16.4 `CheckDeclTT` assembly checklist

Five of six cases are closed (`DeclDefnTT`, `DeclThmTT`,
`DeclOpaqueTT`, `DeclAxiomTT`, `DeclBasisTT`).  The sixth needs
`DeclIndTT` to build one `EnvTT.cons` per block member, supplying:

* `hheadRec` ← the bottoms (**now with the `IotaIndexPin` premise
  available as a hypothesis** — producers are only helped);
* `hheadEta`/`hheadUnit` ← `EtaFoldTT`/`UnitFoldTT` via
  `etaPinsT_of_caps`;
* `hheadCtors`, `hheadProj`, `hheadProjPair`, `hheadEq`, `hheadBasis`,
  `hheadNat`, `hheadDivMod`, `hheadReduce` ← freshness/kind
  arguments, as in `DeclBasisTT`'s six blocks;
* the new `CtorResidualOkT` head obligation.

**Foreseen friction**: `EnvTT.cons` takes ~18 positional arguments
(§14.6.3 lists the order for `extendBasisTT`; `EnvTT.cons`'s is
adjacent and worth writing out before use).  The `hheadRec` binder now
carries one more premise than the six basis blocks needed — they
decline it with `_`, and a modeled block will *consume* it, which is
the first place the sweep's asymmetry shows up in anger.

### 16.5 Working memory a successor cannot recover from the code

**Search the siblings before writing a helper.**  This run wrote two
lemmas that already existed — `denote_instLevels` (§14.7.3) and a
`defEqListP_length` whose answer was in `defEqList_inv`, *twelve lines
above the new code* (§15.5).  Both were caught late.  The inventory to
check first, because the bottoms will want all of it:

* `Setlec/TTVerify/Tele.lean` — `TeleTyped.{toV,appN,spine,rest_eq}`,
  `VTeleTyped.{appN,append,retarget,retarget',teleAlign}`,
  `DenoteSpine.{append,take,drop,length,map,get,snoc_inv}`,
  `denote_mkAppN`, `denote_mkAppN_inv`;
* `Setlec/TTVerify/TeleOpen.lean` — `VExpr.instSeq` + 9 lemmas,
  `openFvars` + 4, `instSeq_instantiate1_in`, `VExpr.inst_mkAppN`,
  `openPisAtFvars_stripPis`,
  `stripPis_instantiate1_fvar_isSome_rev`;
* `Setlec/TTVerify/DeclInd.lean` — `denote_paramSpine`,
  `denote_paramTuple`, `instSeq_paramList`, `instSeq_paramTuple`,
  `paramList_inst`, `paramTuple_inst`, `instSeq_len_succ`,
  `instSeqV_len_succ`, `PiTower.*`, `teleAlign_of_stripPis`,
  `eqSlotSort_of_sortPin`, `Deq.ofEqThm{,Closed}`;
* `Setlec/TTVerify/Rename.lean` — `denote_renameConsts`, `RenEqT.*`,
  `PiDomsRenEqT.*`;
* `Setlec/Verify/` — `defEqList_inv` (**returns length *and*
  pointwise**), `iotaRec_inv`, `piResidual_{WScoped,looseBVars,
  fvarLeaves}`, `Expr.mkAppN_getApp`, `Expr.stripPis_{snoc,prefix,
  length,instantiate1_eq}`, `ErasedEq.stripPis_inv`,
  `Expr.stripPis_renameConsts_inv`, `Level.{eval_subst,substFn_map_param,
  substFn_map_subst}`.

**And read the *sibling obligation* before writing a helper for
yours** — `hparP` and `hidxG` in `IotaStep.lean` consume the same
inversion and want the same accessors.  That is the sharpened form of
§14.7.3.

**Elaboration gotchas beyond §14.6.3's list**, each of which cost a
cycle here:

* `intro` cannot bind `-`; use `_`.  (So a `-`-sweep of an `intro`
  chain is literally an `_`-sweep.)
* `show T from e` **breaks when `T` ends in an unparenthesised
  lambda**: `((List.range nP).map fun k => …)` swallows the `from`.
  Parenthesise the lambda, or use a `have`.
* A lemma stated at depth `d + nP + c` will **not** `rw` against a goal
  at `d + nP`, defeq or not.  Give such lemmas an explicit depth
  parameter plus `(hdd : dd = d + nP + c)`; likewise an explicit cut
  `(ht : t = c + nP - 1)` for `instSeq`.
* `nP - 1 + 1 = nP` **fails at `nP = 0`**; `instSeq_len_succ` /
  `instSeqV_len_succ` handle it via the empty argument list.  Do not
  case-split on `nP` at every site.
* `obtain rfl : a = b` may eliminate *either* name — check which
  survives before writing the rest of the block (`restCE` survived,
  `restC` did not).
* `congr 1` on `some (.bvar x) = some (.bvar y)` does not reach the
  `Nat`; use `simp only [Option.some.injEq, VExpr.bvar.injEq]; omega`.
* `by_contra` is unavailable (no Mathlib); use
  `rcases Nat.lt_or_ge …`.
* `List.getD_eq_getElem` does not exist; `simp [List.getD,
  List.getElem?_eq_getElem h]` is the idiom, and `List.getElem?_drop`
  is what moves `getD` past a `drop`.
* `defEqList_inv` gives `⟨length, pointwise⟩`; the pointwise part
  arrives with the **left** side as `[i]` and the **right** as
  `getD i default`.  Rewrite only the side that needs it.

**A false lemma is a message.**  Three times now the wrong statement
announced itself rather than merely failing: `SameDoms.refl` (§0),
`TeleAlign.inst` (§15.4's retraction), and
`stripPis_instantiate1_isSome_rev` for a general argument (§15.6).  In
each case a "trivial" step that would not go through was describing
the object.  **Try the trivial lemmas early; the ones that refuse are
the design.**


## 17. The plain bottom, closed — and the slot-sort request, measured

Written at the landing of `IndBottomPlainTT`
(`Setlec/TTVerify/IndBottomPlain.lean`, sorry-free, master `ea9fcea`).
Three things belong on the record: the answer to §16.1's structural
question, the machinery the bottom actually needed (§16.1's budget was
right about the shape and wrong about one prerequisite), and the
request for the one premise still carried.

### 17.1 §16.1(4) answered: the claims are available, the model's way

`modeled_bottom_plain` takes `m₀ : EnvModel V env₀` — the invariant at
the *provisional* environment — and `provisionRecs_sound`
(`Setlec/Model/Extend/Recs.lean`) is what supplies it.  The bridge
does the same: `IndBottomPlainTT` takes `m₀ : EnvTT env₀` plus
`hstep : CheckStepTT` (proved — `checkStepTT`), and derives
`DefEqClaimsTT`/`InferClaimsTT` by `checkSoundTT`.  The assembly owes
the transpose of `provisionRecs_sound` (each rule-less recursor is an
`EnvTT.cons` whose `hheadRec` is vacuous) and of the `SwapList`
transport (the law proved at `env₀` moves to the final environment,
where the recursors differ only in their rule lists, which `denote`
never reads).  **No design question: the model's structure was the
answer.**

### 17.2 What the bottom needed that §16.1 did not list

* **The depth mismatch, and the padding trick.**  The claims return
  `Deq`s in a context of length *exactly* `rP + cnF` (`CtxOk`'s first
  conjunct), while a zipper step at position `n` holds only `n` fitted
  values.  `CtxOk` constrains only the entries its subject's leaves
  reach, so the untouched slots are chosen `.sort 0` and instantiated
  with the closed inhabitant `∀ p : Prop, p` (`CtxSpine.pad`,
  `dummyPropT`) — a strengthening lemma is neither available nor
  needed.  The set model never meets this: a valuation restricts for
  free.
* **The cross-frame instantiation** (`instPisAt_denote_cross`).  The
  kit's constructor runs open `cvj.type` at *scattered* statement
  variables; the fire site walks the denoted tower at its own values.
  One lemma relates them, for any value assignment, with one
  commutation (`instSeq_inst0`) as its whole content.  This is the
  fired form's price for the model's `ctor_pkg_*` machinery, paid
  once.
* **`IotaIndexPin` was under-strong — found by using, as predicted.**
  `mkAppN` decompositions are not unique and `Deq` has no application
  injectivity, so the pin's `getD` facts about an unlocatable split
  could not be aligned with the bottom's own reading of `restC`.  The
  re-signing (master `c16235e`) adds the arity, disjunctively
  (`mI = rP ∨ cargs.length = cnP + (mI - rP)`): with no indices the
  facts are vacuous and the supplier's guard does not determine the
  arity.  Cost: two lines in `rec_rules_fire`; the transports pass the
  pin opaquely and the basis blocks never touch it.
* **Consumers confirmed the fired form's dividend.**  `PlainChecked`'s
  public λ-tower conjuncts (`hopenX`, `hlinst`, `hdeLam`) and the
  theorem's `find?` are *not* hypotheses of the bottom — the fired
  law's right side is the rule's denoted rhs applied to the spine, so
  nothing walks the tower.  (`hopenP`/`hcinstP`/`hdePars` **are**
  needed — the parameter bridge crosses recursor-prefix and
  constructor-parameter domains through the public frame.)

### 17.3 GRANTED (#146, form 2 of §14.7.4): `checkIotaSidesTy` certifies the slot's sort

**Landed 2026-08-27** (task #146; DESIGN.md, "The iota certificate
certifies the slot's sort").  `checkIotaSidesTy` now infers the slot's
type and `isDefEq`s it against `.sort ℓA`, the level threaded from each
of the six call sites' own `Eq`-head match (via the new `eqHeadLevel`
accessor, `Setlec/Kernel/CheckerBase.lean`).  `PlainChecked`,
`NestedChecked` (`Setlec/Verify/Extend/Iota.lean`) and
`checkProjIota_inv` (`Setlec/Verify/Extend/Proj.lean`) carry
`IotaSlotSorted`'s body verbatim as their last conjunct, so each
bottom's `hslot` discharges by `exact` — that swap is still to be
made; until it is, the hypothesis stays.  `IotaSlotSorted`'s own
docstring still reads as a pending request: it is left untouched
deliberately, so that the de-staling lands with the swap rather than
across an in-flight edit of `IndBottom.lean`.  The rest of this section is
the original request, kept for the reasoning.

**The gap.**  Every bottom fires `EqLawTT`, whose first β-step wants
`⊢ ⟦αS⟧ : Sort ⟦ℓA⟧` — the equation slot at the sort its own `Eq.{ℓA}`
names.  Here the slot is a **motive application**, so `StatementSortPin`
(a syntactic pin on the model former's residual) cannot serve it, and
no syntactic pin can: the slot's shape varies per rule.  Inversion
cannot recover it (Π-injectivity is refuted, `Inversion.lean`).

**The ask.**  `checkIotaSidesTy` (`Setlec/Kernel/Modeled.lean`) — which
already holds `ops`, the depth and the slot, and already certifies both
*sides* against it — additionally infers the slot's type and `isDefEq`s
it against `.sort ℓA` at the statement's own equation level; the level
reaches the call from each of the six call sites' own `Eq`-head match.
The carrier `IotaSlotSorted` (`Setlec/TTVerify/IndBottom.lean`) is that
check's inversion shape verbatim, committed in advance so the swap is
`exact`; `PlainChecked`/`NestedChecked` gain the conjunct and the
`checkIotaThm{,N}` inversions forward it.

**The measurement** (temporary probe on the shared
`checkIotaSidesTy`, both paths — it is one function; six call sites
threaded the level; reverted, checker byte-identical, gates re-run
green): whole corpus, arena (incl. `init-prelude`) + e2e:

| calls | slot's sort check passes |
|---|---|
| 3 895 | **3 895 / 3 895** |

Zero counterexamples; the check can only make the checker stricter and
rejects nothing in the corpus.

**Until granted**, `IndBottomPlainTT` (and the nested and projection
bottoms after it) carry `hslot : IotaSlotSorted` as one named
hypothesis each — one supplier, one swap per bottom.

### 17.4 Named in advance: the nested law is missing its parameter premise

Scouted for `IndBottomNestedTT`, recorded before the proof is written.
`RecRulesTT`'s parameter premise is `.plain`-guarded (§14.6.3: a
nested rule's comparands are its stored *pins*, so the plain shape
would be wrong for it) — but no nested-shaped premise was added, and
the nested bottom is the first consumer that needs one: the checked
statement's major applies the constructor to the **pins** at the
statement's prefix, the fired major to arbitrary `ys`, and identifying
`ys.take cnP` with the pins' instantiation is exactly what `iotaRec`'s
comparison (`defEqList (margs.take ctorParams) (recFireComparands …).2`,
nested branch) guards.  Expect a re-signing in the `IotaIndexPin`
pattern: the premise stated over the pins' *opened denotations*
(`openFvars` must relocate to a leaf module first — `EnvTT.lean` cannot
import `TeleOpen.lean`), supplied by `IotaStep.lean` from the guard it
already destructures past, declined with `_` by the basis blocks.

## §18 The `EtaLawTT` + `CtorResidualOkT` increment (third run, task #119)

§16.3, landed in one increment:

* **`EtaLawTT` carries the fabrication's typing as a premise** —
  `EtaRhsTyped`'s body verbatim, bound after the subject's typing.
  `EtaFoldTT` dropped its `hrhs` hypothesis (the binder is the
  premise); `EtaRhsTyped` stays as documentation of the moved binder.
* **`CtorResidualOkT` is an `EnvTT` field** (`ctor_residual`), the
  transpose of #136's `checkCtorResidual`.  One deliberate deviation
  from §16.3's spelled shape: the clause carries **both reservation
  guards** (`T` and `caps.etaCtor` non-reserved), matching `CapsOkTT`'s
  eta clause and `EtaFamilyStoredT`'s first conjunct.  Without them the
  basis blocks cannot refute the head obligation's `etaCtor = ci.name`
  disjunct (nothing else forbids an *old* family from naming a reserved
  constructor), and the only consumer holds both flags anyway.  With
  them, `basisResidVacuous (by decide)` closes all twenty pinned
  installs and `extendPairProjTT` refutes by kind.
* **The supplier lives once, in `structEtaCertWith_stepTT`** — both
  consumers (defeq's `structEtaCert` and `majorToCtor`'s eta rescue)
  route through it, so `MajorStep.lean` needed no change beyond what
  `eta_rescue`'s new `hfabT` hypothesis forces.  The derivation:
  `structEtaCertWith_inv` now exposes #137's constructor-telescope
  certificate (new conjunct between the two `defEqList` halves;
  the inversion already stepped over it), `certs_typed` walks it,
  `DenoteSpine.unique` identifies the walked spine with the law's,
  `TeleTyped.rest_eq` + `piResidual_of_stripPis` (new: `piResidual` at
  full depth = the stripped body under `Expr.instSeq`) compute the
  walked residual, the pin rewrites it to `directFam`, and
  `Expr.instSeq_bvar`/`instSeq_mkAppN`/`substFn_map_subst`/
  `substFn_map_param` reduce it to `T p⃗` at the law's levels.
* `extendValueTT` gained `hc₀nctor` (a value install is not a
  constructor) — the residual head obligation's second disjunct needs
  it; the three callers decline by `nomatch`.

Still open from the queue: `IndBottomNestedTT` (the algebra
prerequisites — `openRev`, `instRevChain`, `denote_openRev`, the
`RecRulesTT` nested premise — are landed; the bottom itself is not),
`ProjBottomTT`, `DeclIndTT`/`CheckDeclTT`.  The block-level discharge
of `ctor_residual` at a modeled install belongs to `DeclIndTT`
(§16.3's threading note stands).

## §19 The nested bottom: state, and an elaboration-scale finding

### 19.1 The finding (task #77-class defect, reported per the tripwire)

**The monolithic bottom-theorem architecture is an elaboration hog.**
Measured on this box: the *landed* `IndBottomPlainTT` (one ~1900-line
theorem) peaks at **13.3 GB RSS** to elaborate; the in-flight nested
mirror (~15% longer, heavier per-position machinery) was observed at
15-28 GB and needed a heartbeat bump to 12.8M.  The cause is
structural, not incidental: a single theorem accumulates hundreds of
hypotheses with large types, and every tactic step re-traverses that
context.  A principled fix — decomposing the bottoms into sealed
per-stage lemmas (the openers bundle, the mixed fit, the zipper, the
pointwise identification), each elaborating in a small context —
applies to the *plain* bottom too and should be its own increment,
with the split points chosen so the parameter lists stay sane
(bundle the frame facts into one structure per frame).

### 19.2 The nested adaptation's state

`Setlec/TTVerify/IndBottomNested.lean` (untracked WIP, header-marked,
not in the umbrella): statement complete, Stages A-F' elaborate.
Landed prerequisites (all on master, gates green):

* `RecRulesTT`'s nested parameter premise + `denote_openRev` /
  `denote_openRev_base` (the §17.4 re-signing arc);
* the chain algebra — `VExpr.instSeq_instRevChain` (hypothesis-free:
  elements to the ambient cut, subject past the chain),
  `instSeq_liftN0`, `instSeq_eq_self_of_bvarsBelow`;
* `openRev_instantiateLevelParams`, `openRev_renameConsts`,
  `Expr.fvarsBelow_of_fvarLeaves` (`OpenRevDenote.lean`);
* the cross lemma and the denote-defined walk generalized from
  fvar-shaped entries to denoted entries (the pins are expressions).

**§16.2's "the delta re-applies the plain machinery verbatim" is
half-true and half-refuted** — a restriction-finding in the
house sense: the index premises and the frame bundles do flow through,
but the parameter positions need genuinely new machinery (the
canonical pin value `instRevChain (xs.take rP) wp` with
`wp := denote ψ rP (openRev 0 rP pin)`, its two frame occurrences
identified through `denote_openRev` + rename/level commutation, and
the mixed fit's parameter steps typed from `TypedListOk` + the
P-run's truncated cross rather than from `hdePars`'s bridge).

What remains in the WIP: the zipper's field-position cross (adapt
`hspIdx`/`hwsCond` to the split spine — pins below `cnP`, variables
above; the ws-condition's pin entries close by `hchain` at
`vals := zs.take n`), Stage J's major identification (pointwise:
`hparN` at the parameter positions through `denote_erasedEq` for the
`ErasedEq` major, fields unchanged), and re-audit of the level story
at the redex head (`hlev`'s nested comparands).  Estimated ~300-500
lines on top of the WIP — but do the §19.1 restructure first.

## §20 The sealed per-stage decomposition, landed (plain side)

§19.1's prescription, first half.  `Setlec/TTVerify/IndBottomStages.lean`
holds the plain bottom's four largest blocks as top-level theorems —
`openFrame_deq` (the frame workhorse, `K`-generic), `padHit`,
`paramBridge` (Stage D's bridge), `zipperStage` (Stage G) and
`pointStage` (Stage J's pointwise loop) — each restating its
`have`-block verbatim with the block's free hypotheses as parameters
under their original names; `IndBottomPlainTT` binds them back, so the
extraction is proof-content-neutral (statement unchanged, `git show`
is deletions plus five applications).

**Measured effect** (same polling method as §19.1's baseline):
`IndBottomPlain.lean` 13.3 GB → **3.7 GB** peak RSS;
`IndBottomStages.lean` elaborates at 2.8 GB.  Main proof 1940 → 1084
lines.  The flat-parameter style (30-50 per lemma) turned out to be
cheap to produce — the compiler's unknown-identifier errors enumerate
the block's frontier — and none of the extractions needed proof edits
beyond binding `hcl`/`hopenDeqG`/`hpadhit` in a preamble and adapting
one `hleafS` disjunct shape at the call sites.  Frame-fact *structures*
were not needed for this half; if the nested side's lemma frontiers
get worse, introduce them there.

## §21 `IndBottomNestedTT`, closed on the decomposed shape

The nested bottom landed (`IndBottomNested.lean`, standard three
axioms), built as §16.2 + §19.2 prescribed but on §20's sealed-stage
shape — which is what made it land at **4.0 GB** peak (main proof
~1350 lines) instead of the monolith's 15-28 GB.  The nested stage
lemmas live beside the plain ones in `IndBottomStages.lean`:

* `nestedChain` — a pin's frame value under any fired spine with the
  prefix values is the canonical reverse chain;
* `nestedMixedFit` — Stages D-E sealed: the pins' canonical values
  (`∃ pinVs`, per-index `openRev`-denote + `instRevChain` form) and
  the constructor tower fitted at `pinVs ++ ys.drop cnP`; the
  parameter steps are typed from `TypedListOk` + the truncated P-run
  cross, the field prefix converts through the law's nested premise;
* `zipperStageN`, `pointStageN` — the zipper and pointwise loop with
  the C-run opaque (`ctyN`, denote/closed facts as parameters), the
  scattered spine split (pins below `cnP` with denote+image facts,
  variables above), the major through `ErasedEq` + `denote_erasedEq`
  and the nested head at the stored `lvls`.  Neither needs
  `cnP ≤ rP`.

Two kit additions against §16.2's list, found by proving: the
statement carries `hCstripsHead` (the raw constructor strip's
constant head — `NestedChecked`'s own conjunct) because the residual
arities cross the *pin* substitutions only under a constant head
(`instPisAt_residual_arity_const`, new, with the
`getAppFn`/arity commutation lemmas for `instantiateLevelParams` and
`renameConsts`); and `hlvlsLen` (`lvls.length = cvj.levelParams.length`)
for the level-agreement and head-denote steps.  The assembly reads
both off the install (`nestedRuleShape` / the kit inversion).

#146 landed mid-increment; the bottoms keep `hslot` as the one named
hypothesis and the assembly discharges it by `exact` from the
inversions (`IotaSlotSorted`'s docstring de-staled with this commit,
as agreed).

Remaining: `ProjBottomTT` (§16.3's `cnF = 0` expectation, now against
the sealed plain shape), then `DeclIndTT`/`CheckDeclTT` per §16.4 +
the `ctor_residual` block discharge.

## §22 `ProjBottomTT`: the worked plan (next increment)

§16.3's "`IndBottomPlainTT` at `cnF = 0`" resolves on inspection of
`checkProjFn` to: the stored projection recursor has `mI = rP = nP`
and `ctorParams = nP`, `nfields = nF` — **no index positions**
(`mI - rP = 0`), not no fields.  The direct proof is much smaller than
the plain bottom because on the projection path the statement's
telescope domains are *syntactically* the constructor's renamed
(`domsMatchAux`, a real `==` under `DecidableEq`), which collapses the
zipper:

* **Fit**: build the mixed fit exactly as the plain Stage E does
  (`paramBridge` + the field prefix conversion; with `cnP = rP` the
  mixed spine *is* the fired spine `zs`); then **retarget** it to the
  statement tower via `teleAlign_of_stripPis` (`e := cvj.type`,
  `e' := stmtTy`, `hdoms : PiDomsRenEqT f (nP+nF) cvj.type stmtTy`
  from `domsMatchAux` — no `hdePre`/`hdeFld`/S-frame `hcinst` runs
  exist on this path and none are needed).  The retargeted residual is
  the `openFvars`-opened body's denote; reconcile with Stage A's
  `hRbody` through the canonical-opening `ErasedEq`
  (`instSeq_erasedEq_args`, `Setlec/Verify/Subst.lean`).
* **Fire**: plain Stage A + Stage H verbatim (`hslot` from
  `checkProjIota_inv`'s #146 conjunct).
* **Redex**: pointwise as `pointStage`'s prefix/major branches with no
  index case; the statement redex is
  `f (projFnName T i)` at `fvs.take nP ++ [mk-spine]` (kit hypothesis
  in opened form; the assembly computes the opening of the `==`-pinned
  bvar-level `lhsS`).
* **Reduct** (the one genuinely new piece): the rule's rhs is the
  annotated λ-tower over the constructor's domains returning
  `.bvar (nF - 1 - i)`; `mkAppN RV zs` β-reduces onto the field value
  by `CtxSpine.betaSpine` + `Deq.ofBetaSpine` at `Γj` (the λ-domains
  are the constructor's, syntactically — `checkProjRule`'s second
  `domsMatchAux`).  Needs `stripLams_denoteTele`
  (`openPisAtFvars_denoteTele`'s λ-mirror; the annotation-irrelevant
  opening at `openFvars`, with `stripLams_instantiate1_{isSome,eq}`
  from `Setlec/Verify/Subst.lean`) — sketched, not landed.
* **Kit sources** (all landed checker-side): `checkProjShape` (ctor
  strip + residual arity `nP` + const head — `hclen`/`hCstripsHead`
  analogs), `checkProjRule` (P-frame `hopenP`/`hcinstP`/`hdePars` runs
  verbatim, the λ-tower shape, `hinfR`), `checkProjIota` (statement
  shape pins + `checkIotaSidesTy` + the slot sort), `checkProjTy`
  (public-type closure/telescope).  The syntactic `==` pins become
  `DefEqListOk` runs by `isDefEqCore_rfl`/`DefEqListOk.of_eq`
  (landed, `IndBottomStages.lean`).

Estimated ~600-800 lines against the sealed stages, of which
`stripLams_denoteTele` is ~120.  After it: `DeclIndTT` per §16.4 with
the `ctor_residual` block discharge, then `checkDeclTT_of`.
