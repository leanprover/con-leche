# The sortSpec pilot

A reduction-free **structural** sort function, and the question of
whether its stability theorems can be proved without the fuel/run
apparatus. This file is the pilot's ledger. Seals append.

## Seal 0 — pre-registration, written BEFORE the definition

Three constraints were fixed by reading the existing ledger, not by
discovering them in a failed proof. Recording them here first so the
pilot cannot later claim them as its own findings.

### (P1) Every `Env`-quantified statement carries `EnvWF`

The ledger's bare-`Env` escape (seal 25, `Step2/LevelsInst.lean`;
repeated at seal 64 — *"this campaign has now built the same witness
twice"*). A stored constant with `levelParams = []` whose stored
expression mentions a level parameter anyway is legal input to a bare
`Env` and impossible for a checked one
(`ConstWF.allLevelParamsDefined`).

**This bites sortSpec harder than it bit its predecessors.** sortSpec
reads codomain sorts *through declared types, level-instantiated*.
That is precisely the operation the escape breaks: instantiation has
nothing to act on, and the escaped parameter is answered straight into
the result. So the semantic-soundness statement (2b) and every
level-eval statement is `EnvWF`-premised **from the start** — not
bare-`Env` first and repaired at the third seal.

### (P2) The δ clause must be stated at EVAL'd levels, never syntactically

The brief scopes the "currency lesson" to the conversion-leaf clause
(2d). **It applies to the δ clause (2c) as well**, and the ledger
already contains the falsifier.

The install cert certifies `Level.isEquiv`, **not** syntactic equality
(`Core.lean:1826` is the only sort-sort comparison in the checker and
it is `isEquiv`, never `≤`). So

    def f : Sort (max u v) := PUnit.{max v u}

installs — `isEquiv (max v u) (max u v) = true` is accepted — and the
stored value's structural sort is `max v u` while the declared
codomain is `max u v`. **Syntactically distinct.** The brief's
proposed δ fact, *"stored value's structural sort = declared
codomain"*, is therefore **false as an equation on level expressions**
and must be stated up to eval at ground `φ` (or up to `isEquiv`).

This is the seed that killed the (F) species (DESIGN "STOP: the
w-general (F) species are REFUTABLE — currency finding").

### (P3) …but the (F) species' *second* seed does NOT transfer

The (F) species died twice over: the `max u v` seed above, **and** a
non-sort seed — proof-irrelevance slack, `P x h₁` vs `P x h₂` — which
is why even the level-equivalence-weakened form
(`∃ w', LevelEq w w' ∧ …`) is false there.

**That second seed does not reach sortSpec, and the reason is
structural.** The (F) species transports a fixed witness expression
`w` through a step on an *arbitrary* subject, so it is sensitive to
the arguments. sortSpec reads the **head's declared codomain,
uniformly in arguments** — the no-cumulativity finding's own phrasing
— so `sortSpec (P x h₁)` and `sortSpec (P x h₂)` are equal *by
construction*: neither proof argument is ever inspected.

Argument-blindness is the pilot's structural advantage over the tier
it hopes to retire. It is also exactly what must be checked, not
assumed, at the ι clause, where the motive *is* an argument.

### (P4) Evidential grade — the inherited lesson is PAPER, not a tombstone

`TypeTransportDeltaF` / `TypeTransportCoreF`
(`Annot/SortCoh/Claims.lean:1193` and neighbours) are `def`s —
hypotheses. Their refutation is recorded in DESIGN as a described,
"arena-realizable" falsifier *checked against construction*. **It was
never mechanized.** There is no `not_typeTransportDeltaF` in the tree;
the `SortCoh/` directory holds no falsifier module.

So (P2) is inherited on a paper argument, at a different evidential
grade from this campaign's ninety-odd mechanized tombstones. The
argument is concrete and I believe it. But if the δ clause turns out
to be where sortSpec's wall stands, **mechanizing that falsifier is
part of the pilot's job** — converting inherited prose into a
tombstone is this campaign's standard, and the pilot should not spend
the paper claim as though it were already machine-checked.

### The enabling theorem, re-verified at current line numbers

DESIGN cites `Core.lean:1550`/`1816`; both had drifted. Re-checked on
the merged tree:

* `Core.lean:1560` — `| .sort u => pure (.sort (.succ u))`, `inferBody`'s
  sort clause.
* `Core.lean:1826` — `| .sort u, .sort v => Level.isEquiv u v`, the only
  sort-sort comparison anywhere. No `≤`. No cumulativity.

The set-theoretic side, by contrast, **is** cumulative
(`SetTheory.univ_mono : m ≤ n → univ m ⊆ˢ univ n`). The two sides
disagree about cumulativity, which is a live hazard for the semantic
clause (2b): membership in `univ` is upward-closed, so an *exact*
sort claim is strictly stronger than what the model forces, and a
`≤` claim would be too weak to feed a checker that compares with
`isEquiv`. The statement must land on the exact sort, and the proof
must not be allowed to leak through `univ_mono`.

## Seal 1 — the definition, and where it stops

Four files, all new, all green and warning-free, axioms exactly
`propext`/`Quot.sound`, no `sorry`:

* `SortSpec/Defs.lean` — the definition;
* `SortSpec/Blind.lean` — argument-blindness, discharged;
* `SortSpec/Examples.lean` — worked instances against `inferBody`;
* `SortSpec/Subst.lean` — substitution stability + its refuted
  equational form.

### Finding #0 — the definition is total, structural, fuel-free

Not two mutual functions but **four non-mutual** ones, in dependency
order:

    levelOf : Expr → Option Level
    piCod   : Expr → Nat → Option Level
    ctxCod  : List Expr → Nat → Nat → Option Level
    sortApp : SortEnv → List Expr → Expr → Nat → Option Level

with `sortSpec σ Γ e := sortApp σ Γ e 0`.  `sortApp` recurses only
into **direct subterms** (`app→f`, `forallE→ty,body`, `lam→body`,
`letE→body`), so it is a plain structural recursion; no
`termination_by`, no measure, no fuel, and — because `piCod` and
`ctxCod` never call back — no mutual block at all.

The reason the whole thing collapses to something this small:

> **`piCod` needs no context and no environment.**  The only value it
> ever reads out is a `Level` sitting inside a syntactic `.sort` node,
> and a `Level` contains no expression `bvar`s.

So the sort-context is a plain `List Expr` of binder *type*
expressions with **no de Bruijn shifting anywhere** — entry `i` is
handed to `piCod`, which does not interpret it in any context.  That
single observation is what removes the lifting/weakening apparatus a
context-based sort function would normally need, and it is why the
substitution theorem is as short as it is.

### Where the brief's predicted clauses were wrong

1. **The `.lam` clause is not `imax`-shaped.**  A λ's type is a `Π`,
   and a `Π` is never a sort, so `sortSpec (fun x : T => b) = none` at
   zero arguments — which is exactly what the checker's own `sortOfE`
   answers (`inferBody` gives the λ a `forallE`, `whnf` leaves it a
   `forallE`, `ensureSort` fails).  The `imax` shape belongs to
   `forallE` alone.  What the λ clause *does* is the β-skip, and only
   under at least one argument:
   `sortApp σ Γ (.lam _ A b) (n+1) = sortApp σ (A :: Γ) b n`.
2. **The `.const` clause does not "read its sort" — it walks its
   codomain.**  `.const c us` at `n` arguments must strip `n` binders
   off the *instantiated declared type* before reading anything;
   otherwise every applied type former (`List α`, `Eq a b`) is lost.
   Reading `us.length = levelParams.length` first is not optional: it
   is `inferBody`'s own guard and it is what keeps
   `instantiateLevelParams` meaningful.
3. **`.bvar` cannot read a *level* out of the context.**  The context
   must carry binder **type expressions**, because a `bvar` head can
   be *applied* (`motive t`) and then the walker needs that head's
   Π-telescope.  A `List Level` sort-context loses the ι case
   outright.
4. **`.proj` has no clause.**  A field's sort is the projection
   entry's stored type instantiated at *the subject's type's* level
   arguments — and producing those needs the subject's type as an
   **expression**, which a sort-only walk cannot produce.  `none`.
   This is an architectural limit of `sortSpec`, not a gap in this
   implementation.
5. **`.lit` deviates slightly, in the safe direction.**  The kernel
   guards literals with `natLitSupported`/`strLitSupported` (which
   check `Nat.zero`/`Nat.succ` shapes too); `sortSpec` only asks the
   oracle about `Nat`/`String`.  It is therefore defined on inputs the
   checker rejects for other reasons; it never disagrees where the
   checker accepts.

### The `.const`/`.app` wall — option (b), and a sharper reason

The predicted wall is real, and it is a **termination** wall, not
merely an incompleteness one.  The resolution taken:

**`sortApp` is environment-free.**  The `.const` clause calls an
abstract oracle `σ : Name → List Level → Nat → Option Level`, and the
canonical `constCod env` performs *exactly one* declared-type read
followed by `piCod`.  Where the residual is not a syntactic sort —
`def foo : Alias` with `Alias` a definition unfolding to a sort — the
answer is `none`.

Why not option (a), structural δ through declared types:

* It is not "reduction-free" in any meaningful sense: unfolding a
  constant *to look at its declared type's head constant, and then
  that one's* is a δ chain by another name.
* It has **no termination measure available to this campaign**.  The
  natural one is declaration order, and `EnvWF` does not carry it:
  `EnvWF env := ∀ c ∈ env.consts, ConstWF env c` resolves every
  constant against the *whole* environment, so `def A : B` together
  with `def B : A` satisfies it.  A δ-chaining `sortSpec` would need a
  strictly stronger, *ordered* environment invariant than any this
  campaign has built, threaded into the **definition** — not just its
  theorems.

That last point is (P1) biting one level earlier than seal 0 expected.
Seal 0 said the bare-`Env` escape "bites `sortSpec` harder than it bit
its predecessors" because `sortSpec` reads declared types
level-instantiated.  It bites harder still: over a bare `Env` the
chaining definition does not merely give wrong answers, it **does not
exist**.

The chosen architecture answers (P1) as strongly as it can be
answered: `sortApp_instantiate1` never quantifies over an `Env` at
all, so the escape cannot be constructed against it.  `Env` enters
only when `σ := constCod env`, and the corollary
`sortSpecE_instantiate1` carries `EnvWF env` per (P1) — while saying
plainly that its proof does not use it and structurally cannot need
it.

### (P3) — argument-blindness survives, and it is what costs the ι case

Checked, not assumed, and it holds in the strongest form
(`Blind.lean`):

    sortApp σ Γ (mkAppN f as) n = sortApp σ Γ f (n + as.length)

Only the spine's **length** survives; the arguments are discarded
definitionally.  `sortApp_arg_blind` and `sortApp_letVal_blind` are
`rfl`.  So seal 0's structural advantage over the `(F)` species is
real, and the `(F)` species' second seed (proof-irrelevance slack,
`P x h₁` vs `P x h₂`) provably does not reach `sortSpec`.

**The ι clause pays for it, and the bill is exact.**  For a recursor
head the declared codomain is the motive application `motive t`, not a
syntactic sort, so `piCod` returns `none` after stripping the
arguments (`Examples.lean`, `piCod recTy 2 = none`).  Two different
questions have to be kept apart:

* *the sort of the recursor application's **type***, `motive t` — that
  is `u`, read off the motive binder's declared type, argument-blind,
  and `sortSpec` computes it (`Examples.lean`, the second ι probe);
* *the sort of the recursor application **itself***, i.e. `w` with
  `Nat.rec … t : Sort w`.  This needs `motive t` to *be* a universe.
  That is not pinned by the head at all — `motive := fun _ => Prop`
  and `motive := fun _ => Type 3` give `w = 0` and `w = 3` for the
  same head at the same arity.

So type-valued large elimination is outside `sortSpec`'s reach, and
argument-blindness is precisely the reason.  A `pred` extension —
"`motive t : Sort u` and `motive t` is a universe, so `u = w+1` and
`w = pred u`" — *would* be argument-blind and would recover the case,
but it can only read `pred` off a syntactic `.succ`, and
`max (u+1) (v+1)` is a successor semantically without being one
syntactically.  That is (P2)'s currency lesson again, in a new place;
it is not spent here.

### Wall #1 — substitution stability is NOT an equation

The brief predicted "near-definitional".  Half of that is right.

**Refuted** (`not_sortApp_subst_eq`, a mechanized countermodel, not a
paper argument — cf. (P4)): in the context `(α : Sort 1) (x : α)`,

    sortApp σ ([α] ++ [Sort 1]) (bvar 0) 0                = none
    sortApp σ (substCtx (Sort 0) [α]) (bvar 0) 0          = some 0

The premise is *not* weakened away: the witness satisfies exactly the
hypothesis the theorem uses (`Sort 0 : Sort 1`, verified as `hv₀`).
The phenomenon is real and typed, not an artifact of a junk context:
`x : α` is not structurally a type while `α` is a variable; after
`α := Prop` it is one.  **Substitution creates sorts.**

**Proved** (`sortApp_instantiate1`): the monotone half, and it *is*
near-definitional.

    hv : ∀ Θ m w, piCod A m = some w → sortApp σ Θ v m = some w
    ⊢  sortApp σ (Δ ++ A :: Γ) e n = some w →
       sortApp σ (substCtx v Δ ++ Γ) (e.instantiate1 v Δ.length) n
         = some w

A computed sort is preserved by substitution — the same `Level`
expression, not one up to `isEquiv`, so the (P2) currency hazard does
not arise here.  The whole proof is: one substitution-monotonicity
lemma for `piCod` (`forallE`-stripping commutes with `instantiate1`;
a `.sort u` residual stays `.sort u`), the three-way `bvar` index
split, and structural recursion.  No shifting lemma, no weakening
lemma, no run.

Trap ledger, discharged:

* **bare-`Env` escape** — statement is `Env`-free by construction; the
  `constCod` corollary carries `EnvWF` anyway (P1).
* **smallest instance** — at `Δ = []`, `e = .bvar 0`, `n = 0` the
  theorem *is* its premise `hv`: not trivially true.  At `e = .sort u`
  both sides are `some (.succ u)`: trivially true.  Neither uniformly
  trivial nor degenerate.
* **vacuity** — `hv` is satisfiable (`hv₀`: `A = Sort 1`,
  `v = Sort 0`), and `subst_nonvacuous` exhibits an instance where
  *both* sides are `some (imax 1 1)`.  This is the third time the
  campaign has been asked for this probe; it is a real instance, not a
  restatement.
* **wrong side of a run** — no clause and no premise mentions `whnf`,
  `inferTypeCore`, or a fuel.

### What is NOT yet done

The **agreement theorem** — `sortSpec σ Γ e = some u` implies the
checker's `sortOfE` computes the same `u` — is not proved.
`Examples.lean` checks it instance by instance against `inferBody`'s
clauses, and every clause was designed against them, but that is
evidence, not a proof.  It is the obvious next seal, and it is where
`EnvWF` will finally do work (the `.const` clause's level
instantiation is exactly the operation seal 0 (P1) flagged).

## Seal 2 — agreement proved; and what it does *not* buy

Two new files (`SortSpec/Agree.lean`, `SortSpec/Coverage.lean`), one
umbrella (`Setlec/SetR/SortSpec.lean`) wired into `Setlec/SetR.lean`
so the default `lake build` now covers the pilot (357 jobs, green,
zero warnings), and one seal-1 correction.

### Correction first — seal 1 shipped a wrong clause

`sortApp`'s `.lit` clause returned `σ natName [] 0`: **the sort of the
literal's type name**, i.e. the sort of `Nat`, not of `3`.  A literal
is never a type — `3 : Nat` and `Nat` is not a universe — so the
clause is `none`, and the checker agrees (it infers `Nat` for a
literal, and `whnf Nat` is not a sort, so `sortOfE` fails).

Worth recording *how* it was caught: not by review and not by the
worked instances, but by the agreement proof's clause audit, on the
first pass.  Agreement is the test that has teeth; seal 1's
"evidence, not a proof" caveat was the right one to have written.

### Agreement — PROVED

    noLet e →
    sortSpecE env [] e = some u →
    inferTypeCore μ env F d e = .ok t →
    sortOfE μ env φ (F + 2) d e = some (u.eval φ)

(`sortSpec_agree`; `sortSpec_agree_exists` for the `∃ F` form;
axioms exactly the three standard.)  Read: **`sortSpec` never lies.**
Where it commits to a level, a run that infers anything at all for the
same subject infers exactly that sort — at a *constructively named*
fuel, not an existential one.

The engine is one invariant carried through the fuel induction
(`piCod_agree`): *if `sortApp σ [] e n = some u` and the checker
infers `t` for `e`, then `piCod t n = some u`.*  At `n = 0` that says
`t = .sort u` outright, which is exactly what `sortOfE`'s
whnf-to-a-sort step needs.

**The two theorems seal 1 landed are precisely what moves it**, which
was not designed and is the seal's pleasant surprise:

* the `.app` clause consumes an argument and the checker's residual is
  `body.instantiate1 a` — closed by `piCod_instantiate1`, seal 1's
  substitution-monotonicity lemma;
* `.forallE`/`.lam` open a binder with `.fvar d n ty` — closed by
  `sortApp_instantiate1` at `Δ = []`, and its premise `hv` is **free**
  here, because `sortApp σ Θ (.fvar d n A) m` *is* `piCod A m`
  definitionally.  Opening a binder with its own variable costs
  nothing (`sortApp_open`).

Wall #1's monotone form was the right statement: the equational form
would have been unusable here anyway, since agreement only ever needs
`some w → some w`.

**One restriction: `letE`-free subjects.**  `sortSpec` reads a `let`'s
*annotation* and drops the value; the checker substitutes the value.
Bridging needs `sortApp σ Θ v m = piCod A m`, and the checker supplies
only `defeq (infer v) A` — so recovering it needs **defeq soundness on
sorts**, a run fact.  Seal 2 stops there and restricts the subject
(`noLet`) rather than importing the run apparatus the pilot exists to
avoid.  The restriction is named, decidable, and preserved by binder
opening.

### The `DeltaSortLinked` dependency — ESCAPED, not deferred

The scout's reading was that seal 1's partiality *deferred* the open
gap to this theorem.  It did not.  The agreement proof does not need
`DeltaSortLinked`-strength material, at any strength, and the reason
is structural:

> `sortSpec` commits only when the declared codomain is **already** a
> syntactic `.sort`.  A `.sort` node carries no expression `bvar`s, so
> the checker's argument substitutions cannot touch it, and no δ step
> is ever needed to *expose* it.

`DeltaSortLinked`'s content — unfold a definition and relate its
value's sort to its declared codomain — is about exactly the case
`sortSpec` answers `none` on.  The proof uses no δ, no defeq fact and
no level equivalence; `whnf` enters only as the identity on `.sort`
and on `.forallE` (`whnf_sort_eq`, `whnf_forallE_eq`).

**But name what the escape costs**, because it is not free.  The
*converse* — completeness, "`sortOfE` succeeds ⟹ `sortSpec` commits"
— is not merely unproved, it is **false**: for
`def Alias : Type 1 := Type` and `def Foo : Alias := Nat`,
`sortOfE (.const Foo [])` reduces `Alias` and answers `1`, while
`sortSpec` reads `Foo`'s declared type `.const Alias []`, finds no
syntactic sort, and answers `none`.  *That* statement is where the
`DeltaSortLinked` gap lives, and it is unreachable by refutation
rather than by proof.  (Evidential grade, per (P4): this countermodel
is **described, not mechanized** — building it needs an environment a
`whnf` run can δ-step through.  It is stated here as prose and should
not be spent as a tombstone.)

### The semantic clause (2) — SKIPPED, deliberately

`interp2 : (Nat → V) → AVExpr → V` consumes an **`AVExpr`**, not an
`Expr`, so `interp2 ρ e ∈ˢ univ (sortSpec e)` does not even typecheck
without going through `denote2` — and `denote2`'s binder clauses call
`sortOfE`/`lamSortE`, i.e. *runs*.  Stating the semantic clause would
therefore drag the whole erasure/`denote2` bridge into a pilot whose
entire point is to do without runs.

And it would buy nothing that (1) does not already buy more of.  By
`kind_not_semantic` (`Interp2/Graded.lean`) the tower is cumulative —
`∃ T, T ∈ˢ univ 0 ∧ T ∈ˢ univ 1` — so a membership fixes only a lower
bound and can never be run backwards to pin a level; `univ_inj` says
an *equality* of universes is the only handle.  A membership statement
is strictly one-directional and cannot substitute for agreement.

Skipped, per the increment's own instruction.  Nothing was built for
it.

### The mode question (3) — the pilot genuinely sidesteps seal 10

**Answer: agreement is mode-free.**  `μ` is universally quantified in
`sortSpec_agree`; `sortSpec_agree_noModel` instantiates it at the
official-parity lane to make that visible rather than merely stated.

The premises actually needed are exactly two: `noLet e`, and
`inferTypeCore μ env F d e = .ok t`.  No `mode.verified`.

The reason is architectural, not lucky: the parked `Denote2Total`
needs `lamSortE` defined at every λ node — the *body's* type's sort,
which the checker computes only under `mode.verified`.  `sortSpec`
never asks for it: at a λ it reads the **binder's** type off the term
and pushes it on the sort-context.  `inferBody`'s verified-only block
is a side check; it can make the run fail (and the run's success is a
premise) but it never changes the inferred type, so the `.lam` case
discards it (`-` in the inversion's pattern).  Seal 10's withdrawn
premise is not reintroduced.

`EnvWF` likewise does no work, and this is the seal's second
non-obvious finding.  Seal 1 predicted agreement would be where
`EnvWF` "finally does real work".  It is not: **both sides read the
same declared type through the same `instantiateLevelParams`**, so a
bare-`Env` escape produces identical garbage on both sides.  Agreement
is a *relative* statement, and (P1)'s escape cannot separate the two
functions it relates.  `EnvWF` is carried on the statements because
(P1) binds, and is flagged in the file as unused and structurally
unusable.  It will do real work only in a *semantic* statement, which
seal 2 declined to build.

### Catch-up estimate (4) — the number is 0, and here is why

The tier as it stands (counted, not guessed): `Annot/SortCoh/*` is
**10 files, 19,019 lines, 118 `Prop`-valued species**, of which **90
have an in-tier supplier theorem and 28 do not**.  The 28 include all
five core claims — `EnsureSortAgreeAt` (A), `SortOfAgreeAt` (B),
`SortOfWhnfCoreStableAt` (C), `SortOfDeltaStableAt` (C-δ),
`SortOfWhnfStableAt` (C*) — plus `DefEqE` and `SortLinkE`.

**A landed `sortSpec` retires 0 of the 118 species and 0 of the 5 core
claims.**  Two independent reasons, either sufficient:

1. **Wrong shape.**  SortCoh's obligation is *relational*: two
   subjects `a`, `b` (or `e`, `e'`), a defeq verdict or a reduction
   step between them, and the conclusion that their sort *runs* agree.
   `sortSpec`'s theorem is *absolute*: one subject, structural
   function versus run.  An absolute fact yields a relational one only
   through totality on both sides — and `sortSpec` is not total.
2. **Not total, by four separate walls, each already priced.**
   Recursor applications (the ι wall), `.proj`, `letE`, and any
   constant whose declared codomain is not a syntactic sort
   (δ-chaining).  Every core claim quantifies over arbitrary subjects
   with only scoping/boundedness guards, so each of the four is
   individually fatal to retirement.

What `sortSpec` supplies instead, and it is not nothing:

* On its fragment it gives the **value**, not merely coherence —
  strictly stronger than (B), which only concludes `u = v`.
* On its fragment the **fuel apparatus disappears**.  Claims.lean's
  headline trap is "two independent fuel scales", discharged through
  `KnotFuelDet`; `sortSpec` is fuel-free and agreement names the fuel
  constructively (`F + 2`), so on the fragment the trap does not
  arise.

**The fragment, measured** (`SortSpec/Coverage.lean`, `decide`-checked
on the 26 pinned basis constants):

    answerable c  ↔  c is an inductive type former

| class | count | `sortSpec` | verdict |
|---|---|---|---|
| type formers | 8 | answers | complete |
| ctors + `Quot.sound` | 9 | declines | correct — never types |
| recursors | 9 | declines | the ι wall |

So **8/26 = 31% of the environment's constants are answerable, and
that is 100% of the class that can appear as a binder type**, while
**9/26 = 35% are declined at the ι wall** — declined for a limitation
rather than a fact.

Are the structural incapacities fatal or partial?  Split them:

* `.proj` — **fatal, architecturally**.  A field's sort needs the
  subject's type *expression* (its level arguments); a sort-only walk
  cannot produce one.  Fixing it means building a reduction-free type
  inferencer, i.e. a different pilot.
* type-valued large elimination — **partial**.  A `pred` extension is
  argument-blind and would recover it, but can read `pred` only off a
  syntactic `.succ`, and `max (u+1) (v+1)` is a successor semantically
  without being one syntactically: (P2)'s currency lesson, unspent.
* λ at zero arguments — **not a limitation at all**.  A λ is not a
  type; `sortOfE` fails there too.  Correct, not partial.
* `letE` — **partial**, and cheaply so: one defeq-soundness-on-sorts
  fact would lift the `noLet` restriction.
* δ-chaining — **fatal at the current invariant**.  It needs an
  environment *order*, and `EnvWF` is
  `∀ c ∈ env.consts, ConstWF env c`, which resolves against the whole
  environment and admits `def A : B` with `def B : A`.

Verdict for the memo: `sortSpec` is not a replacement for the
run-level coherence tier and should not be scheduled as one.  It is a
**complete, cheap, fuel-free answer on the type-former fragment**, and
its landed value to the tier is one absolute agreement theorem plus
two substitution lemmas — roughly 700 lines against the tier's 19,019,
overlapping it in zero species.

### Seal 2, addendum — the converse countermodel, MECHANIZED

Seal 2 recorded the converse's falsifier as prose and flagged its own
evidential grade under (P4).  It is now built:
`SortSpec/Converse.lean`, axioms exactly the three standard.

    def Alias : Type 1 := Type      (defnInfo, value `.sort 1`)
    axiom Foo  : Alias              (axiomInfo, type `.const Alias []`)

* `converse_sortOfE` — the checker answers `some 1`.  It infers
  `Alias`, and `whnf` δ-unfolds it to `Sort 1` in two loop iterations
  (peeled with a `whnfLoopFuel_succ`-pattern lemma at depth two, since
  the budget is `irreducible`).
* `converse_sortSpec` — `sortSpec` answers `none`, by `rfl`.  It reads
  `Foo`'s declared type, sees a constant, and declines.
* `not_sortSpec_complete` — the two together refute completeness.
* `converse_gap` — the bare disagreement, one environment, one
  subject: `some 1` against `none`.

**The environment is checker-realizable, not junk.**  `Alias`'s value
`Sort 1` infers `Sort 2`, its declared type on the nose
(`cm_alias_value_types`); `Foo`'s declared type `Alias` infers
`Sort 2`, so it passes the `ensureSort` an axiom's type must
(`cm_foo_type_is_a_type`).  Both `rfl`.  This is the difference
between a refutation and an artifact of malformed input, and it is why
the file bothers to state them.

What the tombstone pins, beyond the fact itself: the gap is
**unreachable by refutation, not merely by proof**.  No strength of a
δ-sort-linking theorem rescues completeness, because the `sortSpec`
side never takes the δ step that would expose the sort.  And it prices
seal 1's `.const` decision exactly — the partiality that let agreement
*escape* `DeltaSortLinked` is the same partiality that makes the
converse false.  One decision, both consequences; there is no version
of `sortSpec` that keeps the first and avoids the second without the
environment-order recursion seal 1 ruled out.

### Disposition — the branch PARKS UNMERGED

Ruled at seal 2's close.  The fragment is verified and complete, but
it has **zero consumers on master**, and the #133 precedent (a
zero-consumer theorem is a dead line) cuts against landing an artifact
nothing reads.

* **Retrieval point**: branch `agent/sortspec-pilot`, tip commit
  recorded in the campaign memo alongside this seal.
* **Build state**: the branch is parked **wired in** — the umbrella
  `Setlec/SetR/SortSpec.lean` is imported from `Setlec/SetR.lean`, so
  the default `lake build` covers all seven pilot modules.  Kept
  deliberately rather than reverted: a parked branch's only job is to
  still be revivable, and that question is *"does it build against
  master?"*, which is only answerable if the default target covers it.
  The cost on master is nil, because the branch is not merged.
* **Landing condition**: if a consumer materializes — the natural one
  is a cheap type-former sort answer on an install path, where
  `answerable ↔ indInfo` means the fragment is exactly the constants
  an install needs — it lands **then, with its consumer**, not before.

Final state: seven modules, ~800 lines, no `sorry`, axioms exactly the
three standard, full build green and warning-free at 358 jobs.
