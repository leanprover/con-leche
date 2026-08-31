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
